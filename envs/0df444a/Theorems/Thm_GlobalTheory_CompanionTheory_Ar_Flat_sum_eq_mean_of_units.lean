-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_sum_eq_mean_of_units
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.sum_eq_mean_of_units
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:55.267995+00:00
-- url     : https://prove2.me/theorems/adf5bd37-33f5-5eb0-8191-39887cef9ad3
-- title:
--   Flat: sum eq mean of units
-- statement:
--   The Flat construction uses the sum eq mean of units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ExistsEqMulMultOfUnits.lean#L81-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ExistsEqMulMultOfUnits.lean#L81-L146

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ExistsEqMulMultOfUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem GlobalTheory.CompanionTheory.Ar.Flat.sum_eq_mean_of_units :
    ∀ (F : Type) [Field F] [NumberField F] (d t : (F →+* ℂ) → ℝ),
      (∀ u : (𝓞 F)ˣ, ∑ σ : F →+* ℂ, Real.log ‖σ ((u : 𝓞 F) : F)‖ * d σ = 0) →
      (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) →
      ∑ σ : F →+* ℂ, t σ * d σ =
        (∑ σ : F →+* ℂ, t σ) / (Module.finrank ℚ F : ℝ) * ∑ σ : F →+* ℂ, d σ := by sorry
