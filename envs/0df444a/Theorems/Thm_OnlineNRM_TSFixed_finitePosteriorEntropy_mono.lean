-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_finitePosteriorEntropy_mono
-- name    : OnlineNRM.TSFixed.finitePosteriorEntropy_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T18:21:38.452422+00:00
-- url     : https://prove2.me/theorems/f16b82d7-b69f-4f60-abbf-24d5076d6f08
-- title:
--   Conditional entropy of a finite probability vector decreases with more information
-- statement:
--   For an ambient-measurable probability vector on a finite type, expected conditional entropy decreases under refinement of the conditioning σ-algebra. The statement also covers conditioning σ-algebras outside the ambient one, using Mathlib’s zero convention for conditional expectation.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem OnlineNRM.TSFixed.finitePosteriorEntropy_mono
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [Fintype α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m₁ m₂ : MeasurableSpace Ω) (hm : m₁ ≤ m₂)
    (w : Ω → α → ℝ)
    (hwmeas : ∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => w ω a))
    (hw0 : ∀ ω a, 0 ≤ w ω a)
    (hwsum : ∀ ω, ∑ a : α, w ω a = 1) :
    @ProbabilityTheory.finitePosteriorEntropy Ω α mΩ inferInstance P m₂ w ≤
      @ProbabilityTheory.finitePosteriorEntropy Ω α mΩ inferInstance P m₁ w := by sorry
