-- Prove2me | Theorems.Thm_MarkovInterference_DQBias_lemma_2
-- name    : MarkovInterference.DQBias.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:04.14963+00:00
-- url     : https://prove2.me/theorems/9255c3c6-638b-4618-b1ba-83911a836b0a
-- title:
--   Lemma 2 (corrected: 1 ≤ C) — group-inverse norm bound from mixing
-- statement:
--   Let $P$ be a primitive finite-state transition matrix with stationary distribution $\rho$. Suppose $C\ge1$, $0<\lambda<1$, and for every nonnegative integer $k$,
--
--   $$\|P^k-\mathbf1\rho^{\top}\|_{1,\infty}\le C\lambda^k.$$
--
--   Then the group inverse satisfies
--
--   $$\|(I-P)^\#\|_{1,\infty}\le\frac{2\log C+1}{1-\lambda}.$$
--
--   This bounds the sensitivity of the stationary distribution by the chain's mixing behavior.
--
--   **Formalization Note** The Appendix F statement lacks $C\ge1$. For a one-state chain, its printed hypotheses allow small positive $C$ that makes the stated upper bound negative. The extra condition repairs that edge case; the paper's p. 14 total-variation version also needs a factor of two when translated to this row norm.
-- source:
--   Farias, Li, Peng, Zheng, Markovian Interference in Experiments, arXiv:2206.02371v2, p. 41, Appendix F, Lemma 2 (corrected domain)

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain

namespace MarkovInterference.DQBias

/-- Appendix F, Lemma 2, p. 41, with the required `1 ≤ C` domain. -/
theorem lemma_2 {S : Type} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (rho : S → ℝ) (C lam : ℝ)
    (hP : IsStochastic P) (hp : IsPrimitive P) (hrho : IsStationaryDist P rho)
    (hC : 1 ≤ C) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hmix : ∀ k : ℕ, norm1inf (P ^ k - onesRho rho) ≤ C * lam ^ k) :
    norm1inf (groupInv P rho) ≤ (2 * Real.log C + 1) / (1 - lam) := by sorry

end MarkovInterference.DQBias
