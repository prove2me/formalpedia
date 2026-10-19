-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_finitePosteriorEntropy_scalar_mono
-- name    : OnlineNRM.TSFixed.finitePosteriorEntropy_scalar_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T18:25:47.90998+00:00
-- url     : https://prove2.me/theorems/e4d318bb-9ebe-4446-8d88-fb9c2ac3edfa
-- title:
--   Scalar conditional entropy decreases under refinement
-- statement:
--   For a measurable [0,1]-valued scalar function, expected entropy of its conditional mean decreases when the conditioning σ-algebra is refined, including when either conditioning σ-algebra is outside the ambient one under Mathlib’s zero convention.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem OnlineNRM.TSFixed.finitePosteriorEntropy_scalar_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m₁ m₂ : MeasurableSpace Ω) (hm : m₁ ≤ m₂)
    (f : Ω → ℝ)
    (hfmeas : @Measurable Ω ℝ mΩ inferInstance f)
    (hf0 : ∀ ω, 0 ≤ f ω)
    (hf1 : ∀ ω, f ω ≤ 1) :
    ∫ ω, Real.negMulLog ((P[fun ω' => f ω' | m₂]) ω) ∂P ≤
      ∫ ω, Real.negMulLog ((P[fun ω' => f ω' | m₁]) ω) ∂P := by sorry
