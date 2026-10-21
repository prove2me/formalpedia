-- Prove2me | Theorems.Thm_MarkovInterference_DQBias_eq_6
-- name    : MarkovInterference.DQBias.eq_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:40.084609+00:00
-- url     : https://prove2.me/theorems/cd5cea93-4d92-49ee-b106-89a8fdb4d400
-- title:
--   Eq. (6) (corrected) — ATE expansion and bounded remainder
-- statement:
--   Let $P_0=P_{1/2}-\delta A$ and $P_1=P_{1/2}+\delta A$ be the transition matrices of the control and intervention policies, with stationary laws $\rho_0,\rho_1$, and let $\rho_{1/2}$ be stationary for $P_{1/2}$. Put $G=(I-P_{1/2})^\#$ and suppose $\|A\|_{1,\infty}\le1$. For every $K\ge0$, define the remainder coefficient
--
--   $$a_K=\rho_1^{\top}(AG)^{K+1}r_1-\rho_0^{\top}((-A)G)^{K+1}r_0.$$
--
--   If $C\ge1$, $0<\lambda<1$, and $\|P_{1/2}^k-\mathbf1\rho_{1/2}^{\top}\|_{1,\infty}\le C\lambda^k$ for all $k\ge0$, then
--
--   $$\mathrm{ATE}=\sum_{k=0}^{K}\delta^k\bigl[\rho_{1/2}^{\top}(AG)^kr_1-\rho_{1/2}^{\top}((-A)G)^kr_0\bigr]+\delta^{K+1}a_K,$$
--
--   $$|a_K|\le 2\left(\frac{2\log C+1}{1-\lambda}\right)^{K+1}r_{\max}.$$
--
--   The expansion identifies the first two terms that the differences-in-Q value recovers.
--
--   **Formalization Note** The paper's displayed remainder bound uses its p. 14 total-variation version of Lemma 2, which misses a factor of two. This corrected statement uses the Appendix F row-norm mixing premise and $C\ge1$. The sign in the control term is $((-A)G)^k$, including for even $k$.
-- source:
--   Farias, Li, Peng, Zheng, Markovian Interference in Experiments, arXiv:2206.02371v2, p. 14, Eq. (6) and preceding remainder bound (corrected premise)

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain
import Definitions.Def_MarkovInterference_DQBias_MDP

namespace MarkovInterference.DQBias

/-- Equation (6), p. 14, with the corrected hypothesis for its remainder bound. -/
theorem eq_6 {S : Type} [Fintype S] [DecidableEq S]
    (M : MDP S) (rho rho0 rho1 : S → ℝ) (A : Matrix S S ℝ)
    (C lam δ : ℝ) (K : ℕ)
    (hp0 : IsPrimitive (M.P 0)) (hp1 : IsPrimitive (M.P 1))
    (hph : IsPrimitive M.Phalf)
    (hrho : IsStationaryDist M.Phalf rho)
    (hrho0 : IsStationaryDist (M.P 0) rho0)
    (hrho1 : IsStationaryDist (M.P 1) rho1)
    (hP0 : M.P 0 = M.Phalf - δ • A)
    (hP1 : M.P 1 = M.Phalf + δ • A)
    (hA : norm1inf A ≤ 1)
    (hC : 1 ≤ C) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hmix : ∀ k : ℕ, norm1inf (M.Phalf ^ k - onesRho rho) ≤ C * lam ^ k) :
    let G := groupInv M.Phalf rho
    let aK := Matrix.vecMul rho1 ((A * G) ^ (K + 1)) ⬝ᵥ M.rvec 1 -
      Matrix.vecMul rho0 (((-A) * G) ^ (K + 1)) ⬝ᵥ M.rvec 0
    M.ate rho0 rho1 =
      (∑ k ∈ Finset.range (K + 1), δ ^ k *
        (Matrix.vecMul rho ((A * G) ^ k) ⬝ᵥ M.rvec 1 -
          Matrix.vecMul rho (((-A) * G) ^ k) ⬝ᵥ M.rvec 0)) +
        δ ^ (K + 1) * aK ∧
      |aK| ≤ 2 * ((2 * Real.log C + 1) / (1 - lam)) ^ (K + 1) * M.rmax := by sorry

end MarkovInterference.DQBias
