-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_mem_sqs_sUnits_iff_isSquare
-- name    : GlobalTheory.QNorm.mem_sqs_sUnits_iff_isSquare
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:08:23.936273+00:00
-- url     : https://prove2.me/theorems/ecd3f9ad-bcd6-4363-8faf-ed4bc969c929
-- title:
--   QNorm: mem sqs s Units iff is Square
-- statement:
--   The QNorm construction uses the mem sqs s Units iff is Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsAuxiliaryPlacesSquarePatternsSUnits.lean#L33-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsAuxiliaryPlacesSquarePatternsSUnits.lean#L33-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPlaceIsSquareAndNotIsSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAuxiliaryPlacesSquarePatternsSUnits
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

theorem GlobalTheory.QNorm.mem_sqs_sUnits_iff_isSquare (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) (hx : x ∈ sUnits F S) :
    x ∈ sqs (sUnits F S) ↔ IsSquare (x : F) := by sorry
