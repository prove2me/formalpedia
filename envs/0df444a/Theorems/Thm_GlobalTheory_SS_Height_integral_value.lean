-- Prove2me | Theorems.Thm_GlobalTheory_SS_Height_integral_value
-- name    : GlobalTheory.SS.Height.integral_value
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:53:10.028875+00:00
-- url     : https://prove2.me/theorems/5193bb85-bc60-4763-9aff-16f753d0cf50
-- title:
--   Height: integral value
-- statement:
--   The Height construction uses the integral value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperScheme.lean#L40-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperScheme.lean#L40-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Height
open IsLocalRing
variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem GlobalTheory.SS.Height.integral_value (O : ValuationSubring K) {X : Scheme.{0}} (b : Sp O ⟶ X) (U : X.Opens)
    (h : b (closedPoint O) ∈ U) :
    (spMap O.subtype ≫ b) (closedPoint K) ∈ U ∧ ∀ f : Γ(X, U), ∃ a : O,
      (a : K) = ev K (gs (spMap O.subtype ≫ b) (closedPoint K) U f) ∧
        (IsUnit a ↔ b (closedPoint O) ∈ X.basicOpen f) := by sorry
