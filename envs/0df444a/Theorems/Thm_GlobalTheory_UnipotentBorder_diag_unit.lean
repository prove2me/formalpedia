-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_diag_unit
-- name    : GlobalTheory.UnipotentBorder.diag_unit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:25:21.183954+00:00
-- url     : https://prove2.me/theorems/d09d28f5-d380-41bd-a785-e5095dd12470
-- title:
--   Unipotent Border: diag unit
-- statement:
--   The Unipotent Border construction uses the diag unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L151-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L151-L172

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

theorem GlobalTheory.UnipotentBorder.diag_unit [IsLocalRing O] {β : O} (hβ : ¬IsUnit β) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) O) (hg : IsUnit g.det) (hlow : ∀ i j, j < i → β ∣ g i j)
    (i : Fin n) : IsUnit (g i i) := by sorry
