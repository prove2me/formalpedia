-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_congruenceCondition_mul
-- name    : GlobalTheory.CompanionTheory.HCdecomp.congruenceCondition_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:30.926095+00:00
-- url     : https://prove2.me/theorems/212b122f-5622-429a-a9c9-a98b3f546477
-- title:
--   HCdecomp: congruence Condition mul
-- statement:
--   The HCdecomp construction uses the congruence Condition mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L98-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L98-L108

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

theorem GlobalTheory.CompanionTheory.HCdecomp.congruenceCondition_mul {E : Fin n → Fin n → Module.End ℂ V} {T S : Module.End ℂ V} (hT : T ∈ PP E)
    {m : ℕ} (hS : adH E S = (m : ℂ) • S) : T * S ∈ PP E := by sorry
