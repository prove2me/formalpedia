-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_lift_cre
-- name    : GlobalTheory.CompanionTheory.KoszulBd.lift_cre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:44.248369+00:00
-- url     : https://prove2.me/theorems/c5b9b024-a609-41ad-9d79-cd8ac14ff022
-- title:
--   Koszul Bd: lift cre
-- statement:
--   The Koszul Bd construction uses the lift cre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CommuteOfUnitaryConjugate.lean#L145-L152

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

theorem GlobalTheory.CompanionTheory.KoszulBd.lift_cre (T : Module.End ℂ V) (i : NC ε) :
    Commute (lift ε T : Module.End ℂ (Ch ε V)) (cre i) := by sorry
