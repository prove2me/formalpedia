-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_Supplement_lemma_5_10
-- name    : MultiSpinCounting.Positive.Supplement.lemma_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:29:07.991266+00:00
-- url     : https://prove2.me/theorems/901ea2ec-dd0a-499c-9609-6544d7f8a2a2
-- title:
--   Lemma 5.10 (used in the proof of Theorem 1.7) — incident volume
-- statement:
--   Fix $0<\eta<1$, real $d\ge8$, and integer $q\ge(2+\eta)d$, with (5.13)–(5.15). Put $H_D=\{v:\deg_G(v)>\lfloor(d+q)/3\rfloor\}$ and
--   $$C_d=2+d(e-1)+\frac{d(e^2-1)}4,\qquad C_{\rm vol}=4C_d+4\log d+14.$$
--   There exists a positive integer $N$, depending only on these fixed parameters, such that every $n\ge N$ satisfies
--   $$\mathbb P_{G\sim G(n,d/n)}\!\left[\forall C\text{ component of }G[H_D],\quad |C|\le4\log n\ \Longrightarrow\ \sum_{v\in C}\deg_G(v)\le C_{\rm vol}\log n\right]\ge1-\tfrac12n^{-4}.$$
--   The degrees in the sum belong to the entire graph. This controls the incident volume and hence the sizes of block boundaries.
--
--   Differences from the source:
--   - generalization: the standing assumption d ≥ d0(η) → d ≥ 8 and the explicit estimates (5.13)–(5.15); reason: Lemma B.1 supplies all these inequalities for the source regime; the proofs use only these consequences
--   - encoding: all sufficiently large n → an existential positive natural threshold N; reason: N can be enlarged to exceed d, so the published clamp is eventually the identity
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 26, Lemma 5.10

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Supplement_RandomGraphs

open scoped Classical

namespace MultiSpinCounting.Positive.Supplement

/-- Lemma 5.10, p. 26: the original-graph incident volume and the exact Cvol. -/
theorem lemma_5_10 (η d : ℝ) (q : ℕ) (hη : 0 < η ∧ η < 1)
    (hd : 8 ≤ d) (hq : (2 + η) * d ≤ (q : ℝ))
    (hparams : ParameterEstimates η d q) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      1 - (n : ℝ) ^ (-4 : ℤ) / 2 ≤
        LPCommunity.SBMRecovery.erProb n (d / n)
          (fun G => ∀ C : (exceptionalGraph G d q).ConnectedComponent,
            ((componentVertices G d q C).card : ℝ) ≤ 4 * Real.log n →
            (∑ v ∈ componentVertices G d q C, (G.degree v : ℝ)) ≤
              Cvol d * Real.log n) := by sorry

end MultiSpinCounting.Positive.Supplement
