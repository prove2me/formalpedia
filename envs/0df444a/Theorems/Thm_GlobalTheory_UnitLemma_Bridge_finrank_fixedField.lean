-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Bridge_finrank_fixedField
-- name    : GlobalTheory.UnitLemma.Bridge.finrank_fixedField
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:26:24.352349+00:00
-- url     : https://prove2.me/theorems/d089b000-e5fe-4bf1-bf8e-078108487353
-- title:
--   Bridge: finrank fixed Field
-- statement:
--   The Bridge construction uses the finrank fixed Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L13-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L13-L48

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

theorem GlobalTheory.UnitLemma.Bridge.finrank_fixedField {E : Type} [Field E] [CharZero E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x)
    (hne : ∃ y, c y ≠ y) : Module.finrank (fixedField c) E = 2 := by sorry
