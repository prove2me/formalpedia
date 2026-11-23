-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_apply
-- name    : GlobalTheory.CompanionTheory.HCdecomp.adH_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:20.386211+00:00
-- url     : https://prove2.me/theorems/38f36f9b-bbb8-41bb-ab30-a39956c40e1e
-- title:
--   HCdecomp: ad H apply
-- statement:
--   The HCdecomp construction uses the ad H apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L71-L72

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

theorem GlobalTheory.CompanionTheory.HCdecomp.adH_apply (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V) :
    adH E T = HH E * T - T * HH E := by sorry
