-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_HH_comm
-- name    : GlobalTheory.CompanionTheory.HCdecomp.HH_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:20.501317+00:00
-- url     : https://prove2.me/theorems/194d0bd9-f542-4e3e-9bb0-51c7270df905
-- title:
--   HCdecomp: HH comm
-- statement:
--   The HCdecomp construction uses the HH comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L52-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L52-L66

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

theorem GlobalTheory.CompanionTheory.HCdecomp.HH_comm {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) :
    HH E * E a b - E a b * HH E = (((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)) • E a b := by sorry
