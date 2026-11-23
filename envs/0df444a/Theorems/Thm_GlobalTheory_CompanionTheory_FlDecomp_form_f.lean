-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_form_f
-- name    : GlobalTheory.CompanionTheory.FlDecomp.form_f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:14.191627+00:00
-- url     : https://prove2.me/theorems/3686441f-7f64-4089-810a-b9ec3d60c43a
-- title:
--   Fl Decomp: form f
-- statement:
--   The Fl Decomp construction uses the form f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L169-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L169-L173

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

theorem GlobalTheory.CompanionTheory.FlDecomp.form_f (hh : IsHerm s h) (hF : IsFrame h δ e f W) (a b : Fin l → L) {w : V} (hw : w ∈ W) (i : Fin l) :
    h (f i) (∑ j, a j • e j + ∑ j, b j • f j + w) = a i * s δ := by sorry
