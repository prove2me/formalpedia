-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Red_of_low
-- name    : GlobalTheory.CompanionTheory.HCdecomp.Red.of_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:16.469706+00:00
-- url     : https://prove2.me/theorems/f4a5f140-0bc3-4ce4-a683-e7ed6fd8d094
-- title:
--   Red: of low
-- statement:
--   The Red construction uses the of low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L222-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L222-L223

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

theorem GlobalTheory.CompanionTheory.HCdecomp.Red.of_low {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) : Red u := by sorry
