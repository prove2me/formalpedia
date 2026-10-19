-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_integrable_meanDemand_lpObj
-- name    : OnlineNRM.TSFixed.integrable_meanDemand_lpObj
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T14:39:21.852278+00:00
-- url     : https://prove2.me/theorems/3bd684e4-5707-42fc-b465-302f2017e6f9
-- title:
--   Integrability of mean-demand objectives for random simplex selectors
-- statement:
--   For bounded Markov demand and any measurable random subprobability selector X, its objective under the true mean demand is integrable. X may depend arbitrarily on the true parameter and other randomness; independence and LP optimality are unnecessary.
--
--   Proof route: apply `StronglyMeasurable.integral_kernel` to each coordinate projection to establish measurability of meanDemand. Coordinate demand is bounded in absolute value by |dbar i|, so its kernel integral has the same bound. The simplex assumptions imply 0 ≤ X ω k ≤ 1 almost surely. Hence the objective's absolute value is bounded by the finite constant ∑ k, ∑ i, |p i k| * |dbar i|. Integrability follows from measurability and domination by an integrable constant, using `Integrable.mono'`. This removes the analytic justification needed to split integrals of selector gaps in the parent. Empty product or price sets give the zero function; no positivity of dbar is added.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.integrable_meanDemand_lpObj
    {N K : ℕ}
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k)
    {Θ : Type*} [MeasurableSpace Θ]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (hθ : Measurable θ)
    (X : Ω → Fin K → ℝ) (hXmeas : Measurable X)
    (hX : ∀ᵐ ω ∂P, (∀ k, 0 ≤ X ω k) ∧ ∑ k : Fin K, X ω k ≤ 1) :
    Integrable (fun ω => lpObj p (meanDemand F (θ ω)) (X ω)) P := by sorry
