-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_isSquare_mul_of_nonsquare_units
-- name    : GlobalTheory.QNorm.isSquare_mul_of_nonsquare_units
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:25:42.656426+00:00
-- url     : https://prove2.me/theorems/460a1e8a-a9a9-48ba-9c8f-54fea9e9a353
-- title:
--   QNorm: is Square mul of nonsquare units
-- statement:
--   The QNorm construction uses the is Square mul of nonsquare units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSquareMulOfNonsquareUnits.lean#L61-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSquareMulOfNonsquareUnits.lean#L61-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm IsLocalRing
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero

theorem GlobalTheory.QNorm.isSquare_mul_of_nonsquare_units : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), Valued.v (2 : v.adicCompletion F) = 1 → ∀ x y : v.adicCompletion F, Valued.v x = 1 → Valued.v y = 1 → ¬ IsSquare x → ¬ IsSquare y → IsSquare (x * y) := by sorry
