-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_sub_sq_lt_one_of_two_lt_one
-- name    : GlobalTheory.QNorm.exists_sub_sq_lt_one_of_two_lt_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:47.453676+00:00
-- url     : https://prove2.me/theorems/6b9ddcf1-3e06-4c25-8c5c-bf3ddabffc03
-- title:
--   QNorm: exists sub sq lt one of two lt one
-- statement:
--   The QNorm construction uses the exists sub sq lt one of two lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSubSqLtOneOfTwoLtOne.lean#L29-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSubSqLtOneOfTwoLtOne.lean#L29-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
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

theorem GlobalTheory.QNorm.exists_sub_sq_lt_one_of_two_lt_one :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      Valued.v (2 : v.adicCompletion F) < 1 → ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
        ∃ y : v.adicCompletion F, Valued.v y ≤ 1 ∧ Valued.v (x - y ^ 2) < 1 := by sorry
