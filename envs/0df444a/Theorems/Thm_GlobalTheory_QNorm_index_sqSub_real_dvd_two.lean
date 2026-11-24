-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_index_sqSub_real_dvd_two
-- name    : GlobalTheory.QNorm.index_sqSub_real_dvd_two
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:02:21.920099+00:00
-- url     : https://prove2.me/theorems/99c43b97-99c3-427b-be7a-491264bf0518
-- title:
--   QNorm: index sq Sub real dvd two
-- statement:
--   The QNorm construction uses the index sq Sub real dvd two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexUnitsLocalSquaresFiniteRealPlacesLe.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexUnitsLocalSquaresFiniteRealPlacesLe.lean#L15-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsSquareUnderRingHomAdicCompletionLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ProdAbsNormPowValuationTwoLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardRingHomRealEqNrRealPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe
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

theorem GlobalTheory.QNorm.index_sqSub_real_dvd_two {F : Type} [Field F] (σ : F →+* ℝ) : (sqSub σ).index ∣ 2 := by sorry
