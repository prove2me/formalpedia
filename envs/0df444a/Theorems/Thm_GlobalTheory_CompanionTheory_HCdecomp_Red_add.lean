-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Red_add
-- name    : GlobalTheory.CompanionTheory.HCdecomp.Red.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:14.344572+00:00
-- url     : https://prove2.me/theorems/52892f25-b6a1-4aa1-83fe-03fbf14b7bb8
-- title:
--   Red: add
-- statement:
--   The Red construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L208-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L208-L214

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

theorem GlobalTheory.CompanionTheory.HCdecomp.Red.add {a a' : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (h' : Red a') : Red (a + a') := by sorry
