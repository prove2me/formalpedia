-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_exists_antitone_perm
-- name    : GlobalTheory.CompanionTheory.FlDecomp.exists_antitone_perm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:41:18.085783+00:00
-- url     : https://prove2.me/theorems/80640b4b-7c9b-42ab-99a7-663e07ec3b88
-- title:
--   Fl Decomp: exists antitone perm
-- statement:
--   The Fl Decomp construction uses the exists antitone perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L108-L112

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

theorem GlobalTheory.CompanionTheory.FlDecomp.exists_antitone_perm {n : ℕ} (m : Fin n → ℕ) : ∃ σ : Equiv.Perm (Fin n), Antitone (m ∘ σ) := by sorry
