-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermFrame_frame_cons
-- name    : GlobalTheory.CompanionTheory.HermFrame.frame_cons
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:54.715606+00:00
-- url     : https://prove2.me/theorems/24a1fec7-100a-4872-b79d-7ac01620aff2
-- title:
--   Herm Frame: frame cons
-- statement:
--   The Herm Frame construction uses the frame cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FrameOfAnisotropicPlaneSplitting.lean#L36-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FrameOfAnisotropicPlaneSplitting.lean#L36-L98

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermFrame
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem GlobalTheory.CompanionTheory.HermFrame.frame_cons (hh : IsHerm s h) {δ : L} {e f : V} {U : Submodule L V}
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) (hee : h e e = 0) (hff : h f f = 0) (hef : h e f = δ)
    (hdec : ∀ x, ∃ (a b : L), ∃ w ∈ U, x = a • e + b • f + w) {l : ℕ} {e' f' : Fin l → U}
    {W' : Submodule L U} (hfr : IsFrame (fun x y : U => h x y) δ e' f' W') :
    IsFrame h δ (Fin.cons e fun i => (e' i : V) : Fin (l + 1) → V)
      (Fin.cons f fun i => (f' i : V) : Fin (l + 1) → V) (W'.map U.subtype) := by sorry
