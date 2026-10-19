-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_meanDemand_coordinate_bounds_measurable
-- name    : OnlineNRM.TSFixed.meanDemand_coordinate_bounds_measurable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T14:54:21.423201+00:00
-- url     : https://prove2.me/theorems/386574dc-0885-4459-b938-4451492264c0
-- title:
--   Measurability and interval bounds for mean-demand coordinates
-- statement:
--   Each mean-demand coordinate is measurable in the parameter and belongs to the same closed interval that almost surely bounds the corresponding demand coordinate.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.meanDemand_coordinate_bounds_measurable
    {N K : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (dbar : Fin N → ℝ)
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    (i : Fin N) (k : Fin K) :
    Measurable (fun ρ => meanDemand F ρ i k) ∧
      ∀ ρ, meanDemand F ρ i k ∈ Set.Icc 0 (dbar i) := by sorry
