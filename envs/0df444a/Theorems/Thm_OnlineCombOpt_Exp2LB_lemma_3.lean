-- Prove2me | Theorems.Thm_OnlineCombOpt_Exp2LB_lemma_3
-- name    : OnlineCombOpt.Exp2LB.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:12.210916+00:00
-- url     : https://prove2.me/theorems/b3afc9f7-37ea-47a2-ac39-6d2684b5329c
-- title:
--   Lemma 3, p. 19 — Σ(1 − i/k)C(k,i)²cⁱ / ΣC(k,i)²cⁱ ≥ 1/3 for k ≥ 1 and 1 ≤ c ≤ 2
-- statement:
--   Let $k\ge 1$ be an integer and let $c$ be a real number with $1\le c\le 2$. Then
--   $$\frac{\displaystyle\sum_{i=0}^{k}\Bigl(1-\frac ik\Bigr)\binom ki^2c^i}{\displaystyle\sum_{i=0}^{k}\binom ki^2c^i}\;\ge\;\frac13 .$$
--
--   Equivalently, if $X$ takes the value $i\in\{0,\dots,k\}$ with probability proportional to $\binom ki^2c^i$, then $\mathbb E[1-X/k]\ge 1/3$. The bound is attained at $k=1$, $c=2$. In the proof of Theorem 1 it controls the weight that EXP2 keeps on the suboptimal coordinates against the second adversary of App. A.
--
--   **Formalization Note** The denominator is at least $1$ (its $i=0$ term), so the division is the paper's ratio. The binomial coefficients are natural numbers cast to $\mathbb R$.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 19, Lemma 3

import Mathlib
import Definitions.Def_OnlineCombOpt_Exp2LB_Setting

open Finset

namespace OnlineCombOpt.Exp2LB

/-- Lemma 3 (Audibert, Bubeck, Lugosi, arXiv:1204.4710v2, p. 19): for every integer `k ≥ 1` and
every `1 ≤ c ≤ 2`,
`Σ_{i=0}^k (1 - i/k) C(k,i)² cⁱ / Σ_{i=0}^k C(k,i)² cⁱ ≥ 1/3`. -/
theorem lemma_3 (k : ℕ) (hk : 1 ≤ k) (c : ℝ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    (1 / 3 : ℝ) ≤
      (∑ i ∈ range (k + 1), (1 - (i : ℝ) / k) * ((k.choose i : ℕ) : ℝ) ^ 2 * c ^ i) /
        (∑ i ∈ range (k + 1), ((k.choose i : ℕ) : ℝ) ^ 2 * c ^ i) := by sorry

end OnlineCombOpt.Exp2LB
