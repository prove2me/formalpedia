-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_center_sq_sub_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.norm_center_sq_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:34.029066+00:00
-- url     : https://prove2.me/theorems/7596243b-315e-4568-9444-de9ecda59015
-- title:
--   Finite-Time Centered Energy Decay
-- statement:
--   This statement gives the finite-time Poincaré estimate for the heat semigroup.
--
--   Let $V$, $\nu$, $m$, and $U$ satisfy the heat-model assumptions, with $\nu=m.\operatorname{tilted}(-U)$ and $U\in C^2$. Let $\rho>0$ satisfy
--   $$\rho\|v\|^2\le D^2U(x)[v,v]\qquad(x,v\in V).$$
--   For $u$ in the domain of the closed weighted gradient and $t\ge0$,
--   $$\|\operatorname{center}_\nu u\|^2-
--   \|\operatorname{center}_\nu(P_tu)\|^2
--   \le\frac{1-e^{-2\rho t}}{\rho}\,\|\overline{\nabla}u\|^2,$$
--   where $P_t$ is the heat-semigroup operator.
--
--   This estimate measures the decrease of centered $L^2$ energy over finite time and is the dynamical input for the limiting Poincaré bound.
--
--   **Formalization Note.** The assumption $t\ge0$ is explicit, and the displayed expression is an inequality of real numbers.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_center_sq_sub_le {ρ : ℝ} (hρ : 0 < ρ)
--       (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
--       (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {t : ℝ}
--       (ht : 0 ≤ t) :
--       ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
--           ‖L2.center ν
--             (HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht u)‖ ^ 2 ≤
--         (1 - Real.exp (-2 * ρ * t)) / ρ *
--           ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Curvature`](https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/LogConcave/HeatSemigroup/Basic`](https://prove2.me/theorems/d95536e9-6544-4702-9801-4293ad1362ac), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Supporting theorems: [`norm_sq_sub_norm_apply_sq_le`](https://prove2.me/theorems/d85e3676-603e-4937-ac22-4f0ac1d2765d), [`closedWeightedOperator_center`](https://prove2.me/theorems/7038d041-6a2a-40bc-ab8a-0baeb48cd646), [`closedWeightedOperator_one_eq_zero`](https://prove2.me/theorems/a397e39c-598f-4ce0-b673-0b4857eee9cf), [`mul_norm_closedWeightedOperator_sq_le`](https://prove2.me/theorems/df1ab815-889d-4825-b09c-233d7b8156e8).
--
--   Previous: [`closedWeightedOperator_center`](https://prove2.me/theorems/7038d041-6a2a-40bc-ab8a-0baeb48cd646) · Next: [`literatureConstant_le_of_gap`](https://prove2.me/theorems/b49f19dd-a419-448a-a1a8-ceb4b69486a2).
--
--   [Source excerpt, lines 292–300](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L292-L300) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Curvature.lean#L289-L341 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature`, declaration `FunctionalInequalities.KLS.LogConcave.norm_center_sq_sub_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature

open MeasureTheory Filter Topology InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU

theorem FunctionalInequalities.KLS.LogConcave.norm_center_sq_sub_le_readable {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
        ‖L2.center ν
          (HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht u)‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ *
        ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2 := by sorry
