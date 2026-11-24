-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_lift_gop
-- name    : GlobalTheory.CompanionTheory.DSICFRel.lift_gop
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:29.409343+00:00
-- url     : https://prove2.me/theorems/c78f56c3-6b4b-4ebb-a854-e8be377ce9b5
-- title:
--   DSICFRel: lift gop
-- statement:
--   The DSICFRel construction uses the lift gop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CarImpFrel.lean#L150-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CarImpFrel.lean#L150-L162

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
variable {n : ℕ}
variable {ε : Fin n → Bool} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.DSICFRel.lift_gop (T : Module.End ℂ V) (c d : Fin n) :
    Commute (lift ε T : Module.End ℂ (Ch ε V)) (Gop ε c d) := by sorry
