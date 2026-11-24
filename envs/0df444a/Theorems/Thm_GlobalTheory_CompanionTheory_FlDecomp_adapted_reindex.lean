-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_adapted_reindex
-- name    : GlobalTheory.CompanionTheory.FlDecomp.adapted_reindex
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:41:33.477924+00:00
-- url     : https://prove2.me/theorems/260c98a0-31ec-4328-9d16-aaf4ce618006
-- title:
--   Fl Decomp: adapted reindex
-- statement:
--   The Fl Decomp construction uses the adapted reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L42-L54

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

theorem GlobalTheory.CompanionTheory.FlDecomp.adapted_reindex {h : V → V → L} {l l' : ℕ} {e f : Fin l' → V} {W : Submodule L V} {u : Fin l' → L}
    {Λ : AddSubgroup V} (hA : IsAdapted h e f W u Λ) (τ : Fin l ≃ Fin l') :
    IsAdapted h (e ∘ τ) (f ∘ τ) W (u ∘ τ) Λ := by sorry
