-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_mem_pull
-- name    : GlobalTheory.CompanionTheory.FlDecomp.mem_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:18.667745+00:00
-- url     : https://prove2.me/theorems/ddc04966-ba29-4919-80cc-bdd80108828b
-- title:
--   Fl Decomp: mem pull
-- statement:
--   The Fl Decomp construction uses the mem pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L13-L13

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

theorem GlobalTheory.CompanionTheory.FlDecomp.mem_pull {k : V ≃ₗ[L] V} {Λ : AddSubgroup V} {x : V} : x ∈ pull k Λ ↔ k x ∈ Λ := by sorry
