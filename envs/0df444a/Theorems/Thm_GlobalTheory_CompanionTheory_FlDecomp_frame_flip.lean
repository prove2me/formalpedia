-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_frame_flip
-- name    : GlobalTheory.CompanionTheory.FlDecomp.frame_flip
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:41:15.462364+00:00
-- url     : https://prove2.me/theorems/57df2e0e-68a1-4f19-9e4e-bc557ed67872
-- title:
--   Fl Decomp: frame flip
-- statement:
--   The Fl Decomp construction uses the frame flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L322-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L322-L344

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

theorem GlobalTheory.CompanionTheory.FlDecomp.frame_flip (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h)
    {u : Fin l → L} {Λ Λ' : AddSubgroup V} (hF : IsFrame h δ e f W)
    (h1 : IsAdapted h e f W (fun _ => 1) Λ) (h2 : IsAdapted h e f W u Λ') (p : L) (n : Fin l → ℤ)
    (hn : ∀ i, ‖u i‖ = ‖p‖ ^ n i) (hp0 : p ≠ 0) :
    ∃ (e' f' : Fin l → V) (m : Fin l → ℕ), IsFrame h δ e' f' W ∧ IsAdapted h e' f' W (fun _ => 1) Λ ∧
      IsAdapted h e' f' W (fun i => p ^ m i) Λ' := by sorry
