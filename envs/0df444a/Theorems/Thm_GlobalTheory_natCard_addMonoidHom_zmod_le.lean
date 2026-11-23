-- Prove2me | Theorems.Thm_GlobalTheory_natCard_addMonoidHom_zmod_le
-- name    : GlobalTheory.natCard_addMonoidHom_zmod_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:57.733491+00:00
-- url     : https://prove2.me/theorems/9800df73-d16d-473d-9ac3-80339d8a7b76
-- title:
--   Global Theory: nat Card add Monoid Hom zmod le
-- statement:
--   The Global Theory construction uses the nat Card add Monoid Hom zmod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NatCardAddMonoidHomZmodLe.lean#L5-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NatCardAddMonoidHomZmodLe.lean#L5-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatCardAddMonoidHomZmodLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.natCard_addMonoidHom_zmod_le (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] [Finite A] :
    Nat.card (A →+ ZMod N) ≤ Nat.card A := by sorry
