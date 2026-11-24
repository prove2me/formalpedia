-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_form_w
-- name    : GlobalTheory.CompanionTheory.FlDecomp.form_w
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:41:01.98381+00:00
-- url     : https://prove2.me/theorems/6470d0f6-d1b8-452b-a6d9-79897cad31f9
-- title:
--   Fl Decomp: form w
-- statement:
--   The Fl Decomp construction uses the form w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L175-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L175-L183

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

theorem GlobalTheory.CompanionTheory.FlDecomp.form_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (a b : Fin l → L) {w v : V} (hw : w ∈ W) (hv : v ∈ W) :
    h v (∑ j, a j • e j + ∑ j, b j • f j + w) = h v w := by sorry
