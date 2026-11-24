-- Prove2me | Theorems.Thm_GlobalTheory_PerfectCompletion_sModEq_iff
-- name    : GlobalTheory.PerfectCompletion.sModEq_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:41:01.978795+00:00
-- url     : https://prove2.me/theorems/7ae0614b-dffd-4a0c-867b-dbe57a6eff3c
-- title:
--   Perfect Completion: s Mod Eq iff
-- statement:
--   The Perfect Completion construction uses the s Mod Eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L47-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PerfectCompletion
variable {V : Type} [CommRing V] (x : V)

theorem GlobalTheory.PerfectCompletion.sModEq_iff {C : Type} [CommRing C] (c : C) (n : ℕ) (u v : C) :
    u ≡ v [SMOD (Ideal.span {c} ^ n • ⊤ : Submodule C C)] ↔ c ^ n ∣ u - v := by sorry
