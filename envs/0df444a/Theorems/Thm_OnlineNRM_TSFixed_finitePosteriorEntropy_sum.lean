-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_finitePosteriorEntropy_sum
-- name    : OnlineNRM.TSFixed.finitePosteriorEntropy_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T18:26:04.91589+00:00
-- url     : https://prove2.me/theorems/f5d9326f-3884-49f5-b51f-b2ceac3f8d1a
-- title:
--   Finite posterior entropy as a sum of scalar integrals
-- statement:
--   For an ambient-measurable finite probability vector, the expected conditional entropy equals the finite sum of the expected scalar entropies of its coordinates.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem OnlineNRM.TSFixed.finitePosteriorEntropy_sum
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [Fintype α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω)
    (w : Ω → α → ℝ)
    (hwmeas : ∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => w ω a))
    (hw0 : ∀ ω a, 0 ≤ w ω a)
    (hwsum : ∀ ω, ∑ a : α, w ω a = 1) :
    @ProbabilityTheory.finitePosteriorEntropy Ω α mΩ inferInstance P m w =
      ∑ a : α, ∫ ω, Real.negMulLog ((P[fun ω' => w ω' a | m]) ω) ∂P := by sorry
