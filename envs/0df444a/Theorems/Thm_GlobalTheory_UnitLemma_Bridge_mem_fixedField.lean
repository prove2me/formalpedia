-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Bridge_mem_fixedField
-- name    : GlobalTheory.UnitLemma.Bridge.mem_fixedField
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:26:06.786337+00:00
-- url     : https://prove2.me/theorems/eba1fe0c-f392-45a4-af13-1199ee7770c1
-- title:
--   Bridge: mem fixed Field
-- statement:
--   The Bridge construction uses the mem fixed Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L11-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Bridge

theorem GlobalTheory.UnitLemma.Bridge.mem_fixedField {E : Type} [Field E] (c : E ≃+* E) (x : E) : x ∈ fixedField c ↔ c x = x := by sorry
