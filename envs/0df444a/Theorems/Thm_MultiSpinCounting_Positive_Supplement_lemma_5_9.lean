-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_Supplement_lemma_5_9
-- name    : MultiSpinCounting.Positive.Supplement.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:28:45.405251+00:00
-- url     : https://prove2.me/theorems/ea7570b3-93e4-4db9-9868-d9aed4eb0393
-- title:
--   Lemma 5.9 (used in the proof of Theorem 1.7) — exceptional-component size
-- statement:
--   Fix $0<\eta<1$, real $d\ge8$, and integer $q\ge(2+\eta)d$, with (5.13)–(5.15). Put $D=\lfloor(d+q)/3\rfloor$ and $H_D=\{v:\deg_G(v)>D\}$. For every positive integer $n$,
--   $$\mathbb P_{G\sim G(n,d/n)}\!\left[\text{every component }C\text{ of }G[H_D]\text{ has }|C|\le4\log n\right]\ge1-\tfrac12n^{-4}.$$
--   There is no added lower bound on $n$. Small exceptional components allow the block computations to remain polynomial in graph size.
--
--   Differences from the source:
--   - generalization: the standing assumption d ≥ d0(η) → d ≥ 8 and the explicit estimates (5.13)–(5.15); reason: Lemma B.1 supplies all these inequalities for the source regime; the proofs use only these consequences
--   - encoding: G(n,d/n) for positive integers n without a stated n ≥ d restriction → the published law clamps its edge probability to [0,1]; reason: it agrees when n ≥ d; for n < d it is the complete graph and (5.13) makes H_D empty
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 25, Lemma 5.9

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Supplement_RandomGraphs

namespace MultiSpinCounting.Positive.Supplement

/-- Lemma 5.9, p. 25. No n ≥ d restriction; the published law clamps d/n. -/
theorem lemma_5_9 (η d : ℝ) (q : ℕ) (hη : 0 < η ∧ η < 1)
    (hd : 8 ≤ d) (hq : (2 + η) * d ≤ (q : ℝ))
    (hparams : ParameterEstimates η d q) (n : ℕ) (hn : 0 < n) :
    1 - (n : ℝ) ^ (-4 : ℤ) / 2 ≤
      LPCommunity.SBMRecovery.erProb n (d / n)
        (fun G => ∀ C : (exceptionalGraph G d q).ConnectedComponent,
          ((componentVertices G d q C).card : ℝ) ≤ 4 * Real.log n) := by sorry

end MultiSpinCounting.Positive.Supplement
