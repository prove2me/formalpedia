-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_mem_JJ_of
-- name    : GlobalTheory.CompanionTheory.HCdecomp.mem_JJ_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:53.077093+00:00
-- url     : https://prove2.me/theorems/d7611c60-54cc-4482-a393-0ffc1ae100d2
-- title:
--   HCdecomp: mem JJ of
-- statement:
--   The HCdecomp construction uses the mem JJ of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L120-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L120-L142

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.HCdecomp.mem_JJ_of {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) {t p : Module.End ℂ V}
    (ht : adH E t = 0) (hp : p ∈ PP E) (h : t - p ∈ JJ E) : t ∈ JJ E := by sorry
