-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_JJ
-- name    : GlobalTheory.CompanionTheory.HCdecomp.adH_JJ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:25.24728+00:00
-- url     : https://prove2.me/theorems/ff219ff4-7872-4793-9132-71f0cf875d42
-- title:
--   HCdecomp: ad H JJ
-- statement:
--   The HCdecomp construction uses the ad H JJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InNOfMem.lean#L90-L93

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

theorem GlobalTheory.CompanionTheory.HCdecomp.adH_JJ {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) :
    JJ E ≤ (JJ E).comap (adH E) := by sorry
