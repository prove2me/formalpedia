-- Prove2me | Theorems.Thm_GlobalTheory_localizedModule_mk_one_eq_zero_iff
-- name    : GlobalTheory.localizedModule_mk_one_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:39.869237+00:00
-- url     : https://prove2.me/theorems/0275970e-0921-46a2-9091-f132ddc08016
-- title:
--   Global Theory: localized Module mk one eq zero iff
-- statement:
--   The Global Theory construction uses the localized Module mk one eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L11-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

theorem GlobalTheory.localizedModule_mk_one_eq_zero_iff (p : Ideal A) [p.IsPrime] (x : M) :
    (LocalizedModule.mk x 1 : LocalizedModule p.primeCompl M) = 0 ↔ ∃ s ∉ p, s • x = 0 := by sorry
