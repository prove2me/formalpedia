-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_frame_perm
-- name    : GlobalTheory.CompanionTheory.FlDecomp.frame_perm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:41:16.202575+00:00
-- url     : https://prove2.me/theorems/2ecdd610-7f0b-43fc-92cf-d9aaf1fc7bec
-- title:
--   Fl Decomp: frame perm
-- statement:
--   The Fl Decomp construction uses the frame perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L220-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L220-L250

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
variable {s : L →+* L} {δ : L} {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

theorem GlobalTheory.CompanionTheory.FlDecomp.frame_perm {δ : L} (hδ : δ ≠ 0) {h : V → V → L} (hh : IsHerm s h) {l : ℕ}
    {e f : Fin l → V} {W : Submodule L V} (hF : IsFrame h δ e f W) (σ : Equiv.Perm (Fin l)) :
    ∃ P : V ≃ₗ[L] V, IsIso h P ∧ (∀ i, P (e i) = e (σ i)) ∧ (∀ i, P (f i) = f (σ i)) ∧ ∀ w ∈ W, P w = w := by sorry
