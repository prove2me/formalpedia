-- Prove2me | Theorems.Thm_GlobalTheory_SS_HtForm_factor_of_const
-- name    : GlobalTheory.SS.HtForm.factor_of_const
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:10:12.82899+00:00
-- url     : https://prove2.me/theorems/358c86ac-d71a-4a57-a921-4f33c3296781
-- title:
--   Ht Form: factor of const
-- statement:
--   The Ht Form construction uses the factor of const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPositiveDefiniteQuadraticFormEndomorphisms.lean#L81-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPositiveDefiniteQuadraticFormEndomorphisms.lean#L81-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesOfFgFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPositiveDefiniteQuadraticFormEndomorphisms
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.HtForm

theorem GlobalTheory.SS.HtForm.factor_of_const {k K : Type} [Field k] [Field K] [Algebra k K] (B : Over (Sp k))
    (x : Over.mk (spMap (algebraMap k K)) ⟶ B) {D : B.left.Opens} (hD : IsAffineOpen D)
    {I : Type} (O : I → ValuationSubring K) (hO : ∀ a : K, (∀ i, a ∈ O i) → a ∈ Set.range (algebraMap k K))
    (hx : Set.range x.left ⊆ D)
    (hb : ∀ i, ∃ b : Sp (O i) ⟶ B.left, spMap (O i).subtype ≫ b = x.left ∧ Set.range b ⊆ D) :
    ∃ c : 𝟙_ (Over (Sp k)) ⟶ B, x = toUnit _ ≫ c := by sorry
