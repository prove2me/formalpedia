-- Prove2me | Theorems.Thm_GlobalTheory_exists_injective_zmod_addMonoidHom
-- name    : GlobalTheory.exists_injective_zmod_addMonoidHom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:16.536369+00:00
-- url     : https://prove2.me/theorems/206085f2-835d-4685-b19b-3bb56b05c41f
-- title:
--   Global Theory: exists injective zmod add Monoid Hom
-- statement:
--   The Global Theory construction uses the exists injective zmod add Monoid Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmod.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmod.lean#L16-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function Cardinal
open GlobalTheory

theorem GlobalTheory.exists_injective_zmod_addMonoidHom {a n : ℕ} (hn : n ≠ 0) (h : a ∣ n) :
    ∃ ι : ZMod a →+ ZMod n, Injective ι := by sorry
