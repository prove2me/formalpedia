-- Prove2me | Theorems.Thm_GlobalTheory_SS_Slope_exists_min
-- name    : GlobalTheory.SS.Slope.exists_min
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:46:56.315215+00:00
-- url     : https://prove2.me/theorems/869dc92f-390f-476f-a928-6bf0c5fc8730
-- title:
--   Slope: exists min
-- statement:
--   The Slope construction uses the exists min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/WeightedOrderSlopeComparison.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/WeightedOrderSlopeComparison.lean#L23-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightedOrderSlopeComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Slope
open MvPowerSeries
variable {k : Type} [Field k]

theorem GlobalTheory.SS.Slope.exists_min (w : Fin 2 → ℕ) (f : MvPowerSeries (Fin 2) k) (hf : f ≠ 0) :
    ∃ s, coeff s f ≠ 0 ∧ (Finsupp.weight w s : ℕ∞) = weightedOrder w f := by sorry
