-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_lift_ann
-- name    : GlobalTheory.CompanionTheory.KoszulBd.lift_ann
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:58.037888+00:00
-- url     : https://prove2.me/theorems/be78c5c6-9685-41cb-86b0-4d848c814cb1
-- title:
--   Koszul Bd: lift ann
-- statement:
--   The Koszul Bd construction uses the lift ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L136-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L136-L143

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfUnitaryConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KoszulBd
open CompanionTheory.D.DSIC
open Formalism.REAL (GlRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.KoszulBd.lift_ann (T : Module.End ℂ V) (i : NC ε) :
    Commute (lift ε T : Module.End ℂ (Ch ε V)) (ann i) := by sorry
