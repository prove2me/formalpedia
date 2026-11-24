-- Prove2me | Theorems.Thm_GlobalTheory_AltCorank_exists_dual
-- name    : GlobalTheory.AltCorank.exists_dual
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:57:17.941949+00:00
-- url     : https://prove2.me/theorems/f200e973-21ae-4190-97e4-7f010b5495e5
-- title:
--   Alt Corank: exists dual
-- statement:
--   The Alt Corank construction uses the exists dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAlternatingFormLeftCorankLeOne.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAlternatingFormLeftCorankLeOne.lean#L53-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlternatingFormLeftCorankLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AltCorank
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.AltCorank.exists_dual (S : Submodule K V) (u : V) (hu : u ∉ S) :
    ∃ φ : V →ₗ[K] K, φ u = 1 ∧ ∀ x ∈ S, φ x = 0 := by sorry
