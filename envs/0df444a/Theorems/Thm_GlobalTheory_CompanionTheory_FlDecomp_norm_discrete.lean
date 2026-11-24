-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_norm_discrete
-- name    : GlobalTheory.CompanionTheory.FlDecomp.norm_discrete
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:41:41.172201+00:00
-- url     : https://prove2.me/theorems/532047da-3af0-4955-8193-8b6eb21e2e23
-- title:
--   Fl Decomp: norm discrete
-- statement:
--   The Fl Decomp construction uses the norm discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L74-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L74-L106

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem GlobalTheory.CompanionTheory.FlDecomp.norm_discrete {p : L} (hp0 : p ≠ 0) (hp1 : ‖p‖ < 1) (hpu : ∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖) {x : L} (hx : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ = ‖p‖ ^ n := by sorry
