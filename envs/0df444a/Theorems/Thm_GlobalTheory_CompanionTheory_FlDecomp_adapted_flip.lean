-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_adapted_flip
-- name    : GlobalTheory.CompanionTheory.FlDecomp.adapted_flip
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:41:43.89592+00:00
-- url     : https://prove2.me/theorems/3129aa1c-2087-442e-a8dc-69c47be4c0bf
-- title:
--   Fl Decomp: adapted flip
-- statement:
--   The Fl Decomp construction uses the adapted flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L261-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L261-L271

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

theorem GlobalTheory.CompanionTheory.FlDecomp.adapted_flip (F : Fin l → Prop) [DecidablePred F] {c : L} (hc : ‖c‖ = 1) {u v : Fin l → L}
    {Λ : AddSubgroup V} (hv : ∀ i, ‖v i‖ = if F i then ‖u i‖⁻¹ else ‖u i‖) (hA : IsAdapted h e f W u Λ) :
    IsAdapted h (fun i => if F i then f i else e i) (fun i => if F i then c • e i else f i) W v Λ := by sorry
