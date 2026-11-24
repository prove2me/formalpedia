-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_isSquare_of_isSquare_residue_odd
-- name    : GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:25:40.993085+00:00
-- url     : https://prove2.me/theorems/13c336e3-4655-4ae3-99f4-b30d14018046
-- title:
--   QNorm: is Square of is Square residue odd
-- statement:
--   The QNorm construction uses the is Square of is Square residue odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSquareMulOfNonsquareUnits.lean#L13-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSquareMulOfNonsquareUnits.lean#L13-L56

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

theorem GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : Valued.v (2 : v.adicCompletion F) = 1)
    (z : v.adicCompletionIntegers F) (hz : Valued.v (z : v.adicCompletion F) = 1)
    (h : IsSquare (residue (v.adicCompletionIntegers F) z)) :
    IsSquare (z : v.adicCompletion F) := by sorry
