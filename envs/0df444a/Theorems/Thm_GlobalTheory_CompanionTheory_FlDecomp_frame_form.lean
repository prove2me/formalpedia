-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_frame_form
-- name    : GlobalTheory.CompanionTheory.FlDecomp.frame_form
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:41:08.635046+00:00
-- url     : https://prove2.me/theorems/86b292bb-ee3e-44ba-9e9f-92e5c17288c2
-- title:
--   Fl Decomp: frame form
-- statement:
--   The Fl Decomp construction uses the frame form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L185-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L185-L197

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

theorem GlobalTheory.CompanionTheory.FlDecomp.frame_form (hh : IsHerm s h) (hF : IsFrame h δ e f W) (a b a' b' : Fin l → L) {w w' : V} (hw : w ∈ W)
    (hw' : w' ∈ W) :
    h (∑ j, a' j • e j + ∑ j, b' j • f j + w') (∑ j, a j • e j + ∑ j, b j • f j + w) =
      ∑ j, a j * s (b' j * δ) + ∑ j, b j * s (a' j * s δ) + s (h w w') := by sorry
