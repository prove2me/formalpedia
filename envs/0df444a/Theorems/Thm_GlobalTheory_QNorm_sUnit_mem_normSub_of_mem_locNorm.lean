-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_sUnit_mem_normSub_of_mem_locNorm
-- name    : GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:23:43.339822+00:00
-- url     : https://prove2.me/theorems/ed26a6a3-3ba9-41ff-b2f9-6825d025ea93
-- title:
--   QNorm: s Unit mem norm Sub of mem loc Norm
-- statement:
--   The QNorm construction uses the s Unit mem norm Sub of mem loc Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SUnitMemGlobalNormOfMemLocalNorms.lean#L84-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SUnitMemGlobalNormOfMemLocalNorms.lean#L84-L175

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

theorem GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), _root_.GlobalTheory.QNorm.admitted F S → δ ∈ _root_.GlobalTheory.QNorm.sUnits F S → ¬ IsSquare (δ : F) → ∀ x ∈ _root_.GlobalTheory.QNorm.sUnits F S, x ∈ _root_.GlobalTheory.QNorm.locNorm F δ S → x ∈ _root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) := by sorry
