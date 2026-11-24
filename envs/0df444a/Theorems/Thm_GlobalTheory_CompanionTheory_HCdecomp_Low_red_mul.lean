-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Low_red_mul
-- name    : GlobalTheory.CompanionTheory.HCdecomp.Low.red_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:14.826895+00:00
-- url     : https://prove2.me/theorems/f6ff1e2b-c7c4-4698-b7c7-e40a202e446d
-- title:
--   Low: red mul
-- statement:
--   The Low construction uses the red mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L238-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L238-L263

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

theorem GlobalTheory.CompanionTheory.HCdecomp.Low.red_mul {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) :
    ∀ p : Fin n × Fin n, Red (u * FreeAlgebra.ι ℂ p) := by sorry
