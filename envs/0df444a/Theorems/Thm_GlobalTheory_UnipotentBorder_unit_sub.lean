-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_unit_sub
-- name    : GlobalTheory.UnipotentBorder.unit_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:25:53.66997+00:00
-- url     : https://prove2.me/theorems/eae45b32-d464-46dd-94ab-65fe9bc03fd3
-- title:
--   Unipotent Border: unit sub
-- statement:
--   The Unipotent Border construction uses the unit sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L139-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]

theorem GlobalTheory.UnipotentBorder.unit_sub [IsLocalRing O] {β : O} (hβ : ¬IsUnit β) {a y : O} (ha : IsUnit a)
    (hy : β ∣ y) (z : O) : IsUnit (a - z * y) := by sorry
