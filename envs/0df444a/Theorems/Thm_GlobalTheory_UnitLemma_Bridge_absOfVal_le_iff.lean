-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Bridge_absOfVal_le_iff
-- name    : GlobalTheory.UnitLemma.Bridge.absOfVal_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:43.482432+00:00
-- url     : https://prove2.me/theorems/950536d8-d5c9-4610-9413-b52b9b2ecd27
-- title:
--   Bridge: abs Of Val le iff
-- statement:
--   The Bridge construction uses the abs Of Val le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L226-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L226-L228

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

theorem GlobalTheory.UnitLemma.Bridge.absOfVal_le_iff {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) (x y : E) :
    absOfVal v x ≤ absOfVal v y ↔ v x ≤ v y := by sorry
