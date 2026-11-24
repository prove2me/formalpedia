-- Prove2me | Theorems.Thm_GlobalTheory_QFam_QConj_of_dvd
-- name    : GlobalTheory.QFam.QConj.of_dvd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:59:18.435861+00:00
-- url     : https://prove2.me/theorems/add79515-b627-4371-a250-607019215f46
-- title:
--   QConj: of dvd
-- statement:
--   The QConj construction uses the of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QAllQConjOfDvd.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QAllQConjOfDvd.lean#L22-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulLevelSubstPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QAllQConjOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.QConj.of_dvd {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {g : ℂ ≃+* ℂ} {f f' : ℍ → ℂ}
    (hf : QConj g N f f') : QConj g N' f f' := by sorry
