-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_exists_eq_mul_mult_of_units
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.exists_eq_mul_mult_of_units
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:18:03.824287+00:00
-- url     : https://prove2.me/theorems/b0caf6d0-8bb2-40db-88a2-22da1734ecb0
-- title:
--   Flat: exists eq mul mult of units
-- statement:
--   The Flat construction uses the exists eq mul mult of units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ExistsEqMulMultOfUnits.lean#L8-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ExistsEqMulMultOfUnits.lean#L8-L79

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_eq_mul_mult_of_units (F : Type) [Field F] [NumberField F]
    (D : InfinitePlace F → ℝ)
    (h : ∀ u : (𝓞 F)ˣ, ∑ w : InfinitePlace F, Real.log (w ((u : 𝓞 F) : F)) * D w = 0) :
    ∃ c : ℝ, ∀ w, D w = c * (mult w : ℝ) := by sorry
