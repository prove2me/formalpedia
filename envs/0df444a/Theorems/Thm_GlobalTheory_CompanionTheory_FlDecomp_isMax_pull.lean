-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_isMax_pull
-- name    : GlobalTheory.CompanionTheory.FlDecomp.isMax_pull
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:41:35.362689+00:00
-- url     : https://prove2.me/theorems/326e20ac-84f2-485e-9a8a-05c6ad159f6a
-- title:
--   Fl Decomp: is Max pull
-- statement:
--   The Fl Decomp construction uses the is Max pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L125-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L125-L145

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

theorem GlobalTheory.CompanionTheory.FlDecomp.isMax_pull {h : V → V → L} {Λ : AddSubgroup V} (hM : IsMax h Λ)
    {g : V ≃ₗ[L] V} (hg : IsIso h g) : IsMax h (pull g⁻¹ Λ) := by sorry
