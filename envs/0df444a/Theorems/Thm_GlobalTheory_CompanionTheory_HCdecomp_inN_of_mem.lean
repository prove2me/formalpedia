-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_inN_of_mem
-- name    : GlobalTheory.CompanionTheory.HCdecomp.inN_of_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:52.801527+00:00
-- url     : https://prove2.me/theorems/380326e7-c11e-44a6-bf22-3a3e8d9005ab
-- title:
--   HCdecomp: in N of mem
-- statement:
--   The HCdecomp construction uses the in N of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L25-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L25-L39

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

theorem GlobalTheory.CompanionTheory.HCdecomp.inN_of_mem (E : Fin n → Fin n → Module.End ℂ V) {y : V} (hy : y ∈ NV E) :
    InN (allT n) E y := by sorry
