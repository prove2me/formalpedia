-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_integral_sq_sub_mul_sq_of_unit
-- name    : GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:17.759908+00:00
-- url     : https://prove2.me/theorems/6d88bff4-21fa-42d4-a3cf-398c925e43a3
-- title:
--   QNorm: exists integral sq sub mul sq of unit
-- statement:
--   The QNorm construction uses the exists integral sq sub mul sq of unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/UnitNormFormAtOddPlace.lean#L30-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/UnitNormFormAtOddPlace.lean#L30-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing Polynomial
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ u : v.adicCompletion F), Valued.v (2 : v.adicCompletion F) = 1 → Valued.v δ = 1 → Valued.v u = 1 → ∃ x ∈ v.adicCompletionIntegers F, ∃ y ∈ v.adicCompletionIntegers F, u = x ^ 2 - δ * y ^ 2 := by sorry
