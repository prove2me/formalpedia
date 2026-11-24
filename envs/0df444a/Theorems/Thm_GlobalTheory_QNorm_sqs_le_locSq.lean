-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_sqs_le_locSq
-- name    : GlobalTheory.QNorm.sqs_le_locSq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:53:23.586017+00:00
-- url     : https://prove2.me/theorems/95bcd5f1-553f-4c0a-9a16-3ee9bdc8a0e5
-- title:
--   QNorm: sqs le loc Sq
-- statement:
--   The QNorm construction uses the sqs le loc Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SUnitMemGlobalNormOfMemLocalNorms.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SUnitMemGlobalNormOfMemLocalNorms.lean#L25-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAuxiliaryPlacesSquarePatternsSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfSUnitLocalSquareFiniteRealPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsUnionSupLocalSquaresEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitMemGlobalNormOfMemLocalNorms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero

theorem GlobalTheory.QNorm.sqs_le_locSq (F : Type) [Field F] [NumberField F]
    (U : Subgroup Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    _root_.GlobalTheory.QNorm.sqs U ≤ _root_.GlobalTheory.QNorm.locSq F S := by sorry
