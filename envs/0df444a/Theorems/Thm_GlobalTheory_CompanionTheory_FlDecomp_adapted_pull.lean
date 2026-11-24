-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_adapted_pull
-- name    : GlobalTheory.CompanionTheory.FlDecomp.adapted_pull
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:41:42.660909+00:00
-- url     : https://prove2.me/theorems/f60230a6-8b41-4e8f-96c9-af84d5076779
-- title:
--   Fl Decomp: adapted pull
-- statement:
--   The Fl Decomp construction uses the adapted pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L33-L40

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

theorem GlobalTheory.CompanionTheory.FlDecomp.adapted_pull {h : V → V → L} {l : ℕ} {e f e' f' : Fin l → V} {W W' : Submodule L V} {u : Fin l → L}
    {Λ : AddSubgroup V} {k : V ≃ₗ[L] V} (hk : IsIso h k) (he : ∀ i, k (e i) = e' i) (hf : ∀ i, k (f i) = f' i)
    (hW : ∀ w ∈ W, k w ∈ W') (hA : IsAdapted h e' f' W' u Λ) : IsAdapted h e f W u (pull k Λ) := by sorry
