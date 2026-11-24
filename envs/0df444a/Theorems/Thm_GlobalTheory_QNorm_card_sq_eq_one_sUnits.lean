-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_card_sq_eq_one_sUnits
-- name    : GlobalTheory.QNorm.card_sq_eq_one_sUnits
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:02:57.04889+00:00
-- url     : https://prove2.me/theorems/6aff5f81-6ac7-4369-a5ad-75b4fd29455c
-- title:
--   QNorm: card sq eq one s Units
-- statement:
--   The QNorm construction uses the card sq eq one s Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresSUnitsNumberField.lean#L21-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexSquaresSUnitsNumberField.lean#L21-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsNumberFieldFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FinrankSUnitsNumberFieldAddOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberField
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

theorem GlobalTheory.QNorm.card_sq_eq_one_sUnits (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Nat.card {a : sUnits F S // a ^ 2 = 1} = 2 := by sorry
