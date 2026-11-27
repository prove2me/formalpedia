-- Prove2me | Theorems.Thm_LLMThroughput_TokenBudget_Supplement_lemma_24
-- name    : LLMThroughput.TokenBudget.Supplement.lemma_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:04:05.865804+00:00
-- url     : https://prove2.me/theorems/bbed7f0c-693e-4f4c-8c80-bc10bb03edcd
-- title:
--   Lemma 24 — block-shift monotonicity for prefill service
-- statement:
--   Let $a>0$, $c\ge0$, $b_0>0$ and $b_{\max}$ be real numbers, and write $t_s=c+a\lceil s/b_0\rceil$. For every pair of nonnegative integers $x,y$ with $x+b_0\le b_{\max}$,
--
--   $$\frac{x+b_0}{t_{x+y+b_0}}\ge\frac{x}{t_{x+y}}.$$
--
--   This is the two-variable block-shift inequality used in the proof of Theorem 10. The decode load $y$ has no upper bound. There is no divisibility hypothesis and no requirement that $x+y+b_0\le b_{\max}$.
--
--   **Formalization Note** The zero-load rate is zero, including when $c=x=y=0$. The block size and token cap may be real; all positive integral source budgets are retained.
--
--   Differences from the source:
--   - generalization: integer block size and token cap → real b_0>0 and real b_max, retaining integer x,y and x+b_0<=b_max; reason: the block-shift identity and inequality apply to real block sizes and specialize to every integral source instance
--   - encoding: nonnegative integers x,y and an empty-load quotient → x,y : Nat with the empty quotient equal to zero, including c=x=y=0; reason: Nat is exactly the nonnegative integer domain; zero tokens provide zero service even for a zero-time empty batch
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, p. 48, Appendix E, Lemma 24

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Supplement_BatchTime

namespace LLMThroughput.TokenBudget.Supplement

theorem lemma_24 (a c b0 bmax : ℝ) (ha : 0 < a) (hc : 0 ≤ c)
    (hb0 : 0 < b0) (x y : ℕ) (hcap : (x : ℝ) + b0 ≤ bmax) :
    (x : ℝ) / batchTime a c b0 ((x : ℝ) + (y : ℝ)) ≤
      ((x : ℝ) + b0) / batchTime a c b0 ((x : ℝ) + (y : ℝ) + b0) := by sorry

end LLMThroughput.TokenBudget.Supplement
