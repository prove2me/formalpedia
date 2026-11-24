-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_permMap_apply
-- name    : GlobalTheory.CompanionTheory.FlDecomp.permMap_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:41:03.959396+00:00
-- url     : https://prove2.me/theorems/b0b2f644-2450-4a8a-a949-d9e5b7d42673
-- title:
--   Fl Decomp: perm Map apply
-- statement:
--   The Fl Decomp construction uses the perm Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L203-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L203-L218

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

theorem GlobalTheory.CompanionTheory.FlDecomp.permMap_apply (hδ : δ ≠ 0) (hh : IsHerm s h) (hF : IsFrame h δ e f W) (τ : Equiv.Perm (Fin l))
    (a b : Fin l → L) {w : V} (hw : w ∈ W) :
    permMap hh δ e f τ (∑ j, a j • e j + ∑ j, b j • f j + w) =
      ∑ j, a (τ.symm j) • e j + ∑ j, b (τ.symm j) • f j + w := by sorry
