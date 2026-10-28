-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_literatureConstant_le_inv_of_tendsto_readable
-- name    : FunctionalInequalities.KLS.LogConcave.literatureConstant_le_inv_of_tendsto_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:56.113524+00:00
-- url     : https://prove2.me/theorems/ad4697ec-e48c-433b-b18f-ec34a0341e53
-- title:
--   Poincaré Bound From Curvature And Ergodicity
-- statement:
--   This formalizes the ergodic-interface form of Proposition 4.8.1 of Bakry–Gentil–Ledoux (2014), p. 212.
--
--   Let $V$, $\nu$, $m$, and $U$ satisfy the heat-model assumptions, with $\nu=m.\operatorname{tilted}(-U)$ and $U\in C^2$. Let $\rho>0$ satisfy
--   $$\rho\|v\|^2\le D^2U(x)[v,v]\qquad(x,v\in V).$$
--   Assume that for every $u\in D(\overline{\nabla})$, the centered heat evolution converges in norm:
--   $$\|\operatorname{center}_\nu(P_tu)\|\longrightarrow0\qquad(t\to\infty).$$
--   Then
--   $$C_P(\nu)\le\operatorname{ofReal}(\rho^{-1}).$$
--
--   This declaration isolates the passage from a finite-time curvature estimate and an explicit ergodicity hypothesis to the Poincaré constant bound.
--
--   **Formalization Note.** The conclusion is in `ENNReal`; `ENNReal.ofReal` is applied to the real number $\rho^{-1}$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem literatureConstant_le_inv_of_tendsto {ρ : ℝ} (hρ : 0 < ρ)
--       (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
--       (herg : ∀ u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
--         Tendsto (fun t : ℝ => ‖L2.center ν (Generated.apply
--           (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
--           (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi)
--           (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) t u)‖)
--           atTop (𝓝 0)) :
--       Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Curvature`](https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1), [`Analysis/Semigroup/Generated/Basic`](https://prove2.me/theorems/7707da62-8003-4b5c-8964-af18be8f9082), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Supporting theorems: [`literatureConstant_le_of_gap`](https://prove2.me/theorems/b49f19dd-a419-448a-a1a8-ceb4b69486a2), [`norm_center_sq_sub_le`](https://prove2.me/theorems/7596243b-315e-4568-9444-de9ecda59015).
--
--   Previous: [`literatureConstant_le_of_gap`](https://prove2.me/theorems/b49f19dd-a419-448a-a1a8-ceb4b69486a2) · Next: [`closedWeightedOperator_eq_zero_iff`](https://prove2.me/theorems/245eb849-5b26-4814-9a95-03fa2537cb37).
--
--   [Source excerpt, lines 400–408](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L400-L408) · Frozen source `408915f`.
-- source:
--   Source: Bakry–Gentil–Ledoux, Analysis and Geometry of Markov Diffusion Operators (Springer 2014, Grundlehren der mathematischen Wissenschaften 348 (DOI 10.1007/978-3-319-00227-9), Chapter 4), Proposition 4.8.1 (Poincaré inequality under CD(ρ, ∞)), p. 212. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L396-L494 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature`, declaration `FunctionalInequalities.KLS.LogConcave.literatureConstant_le_inv_of_tendsto`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU

theorem FunctionalInequalities.KLS.LogConcave.literatureConstant_le_inv_of_tendsto_readable {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (herg : ∀ u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      Tendsto (fun t : ℝ => ‖L2.center ν (Generated.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi)
        (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) t u)‖)
        atTop (𝓝 0)) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹ := by sorry
