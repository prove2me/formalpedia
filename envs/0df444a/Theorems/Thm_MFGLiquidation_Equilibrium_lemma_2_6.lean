-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_lemma_2_6
-- name    : MFGLiquidation.Equilibrium.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:39.937269+00:00
-- url     : https://prove2.me/theorems/ffccb5c4-33a2-4063-a1da-2bf2acd7324d
-- title:
--   Lemma 2.6 — for 𝔭 = 0 the FBSDE (2.11) is uniquely solvable, with an explicit solution
-- statement:
--   Assume Assumption 2.3, let $(A,Z^A)$ solve the singular Riccati BSDE and let $0<\gamma<\alpha\wedge\frac12$. For $\mathfrak p=0$ and every $f\in L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R)$, the FBSDE (2.11) has a solution in $\mathcal H_\alpha\times\mathcal H_\gamma\times D^2_{\mathbb F}([0,T])\times L^2_{\mathbb F}([0,T];\mathbb R^m)\times L^2_{\mathbb F}([0,T-];\mathbb R^m)$, any two solutions in this class agree, and every such solution is given by
--   $$B_t=\mathbb E\Big[\int_t^Tf_s\,e^{-\int_t^s(2\eta_r)^{-1}A_r\,dr}ds\ \Big|\ \mathcal F_t\Big],\quad t\in[0,T],$$
--   $$X_t=\mathcal Xe^{-\int_0^t(2\eta_r)^{-1}A_r\,dr}-\int_0^t(2\eta_s)^{-1}B_se^{-\int_s^t(2\eta_r)^{-1}A_r\,dr}ds,\quad t\in[0,T),$$
--   $$Y_t=A_tX_t+B_t,\quad t\in[0,T).$$
--   This is the starting point $\mathfrak p=0$ of the method of continuation: without the mean-field term the system decouples into a linear ODE for $X$ and a linear BSDE for $B$.
--
--   **Formalization Note** The paper states the formula for $X_t$ on $[0,T]$; at $t=T$ the inner integrals $\int_s^T A_r/(2\eta_r)dr$ diverge, and the Lean integral of a non-integrable function is $0$, so the formula is stated for $t<T$; $X_T=0$ follows from $X\in\mathcal H_\alpha$. The formulas hold a.s. for each $t$ ($B$) and a.s. simultaneously for all $t<T$ ($X$). "$Z^B$ and $Z^Y$ are given by the martingale representation theorem" is not a separate claim: their existence is part of being a solution. Uniqueness is with the relation $Y=AX+B$ as part of the solution concept (see the definition of (2.11)).
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 11, Lemma 2.6

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting
import Definitions.Def_MFGLiquidation_Equilibrium_Decoupled

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem lemma_2_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (D : Data Ω k) (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hR : IsSingularRiccati hD A ZA)
    (γ : ℝ) (hγ0 : 0 < γ) (hγα : γ < D.alpha P) (hγ2 : γ < 1 / 2) :
    UniquelySolvable211 hD A γ 0 ∧
    ∀ (f X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      L2F (filtF hD) P D.T f → ClassFBSDE211 hD γ X B Y ZB ZY →
      SolvesFBSDE211 hD A 0 f X B Y ZB ZY →
      (∀ t ≤ D.T, B t =ᵐ[P] P[fun ω => ∫ s in Set.Icc (t : ℝ) D.T, f s.toNNReal ω *
          Real.exp (-∫ r in Set.Icc (t : ℝ) s, A r.toNNReal ω / (2 * D.η r.toNNReal ω)) |
        filtF hD t]) ∧
      (∀ᵐ ω ∂P, ∀ t < D.T, X t ω =
        D.𝒳 ω * Real.exp (-∫ r in Set.Icc (0 : ℝ) t, A r.toNNReal ω / (2 * D.η r.toNNReal ω)) -
        ∫ s in Set.Icc (0 : ℝ) t, B s.toNNReal ω / (2 * D.η s.toNNReal ω) *
          Real.exp (-∫ r in Set.Icc s t, A r.toNNReal ω / (2 * D.η r.toNNReal ω))) ∧
      (∀ t < D.T, Y t =ᵐ[P] fun ω => A t ω * X t ω + B t ω) := by sorry

end MFGLiquidation.Equilibrium
