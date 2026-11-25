-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_field_of_definition_of_point
-- name    : GlobalTheory.T.exists_field_of_definition_of_point
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:20.270213+00:00
-- url     : https://prove2.me/theorems/955af092-4734-43b2-b6ab-53745386ae2a
-- title:
--   T: exists field of definition of point
-- statement:
--   The T construction uses the exists field of definition of point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFieldOfValuesStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFieldOfValuesStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfValues
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfValuesStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_field_of_definition_of_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X), ∃ E : Subfield Ω, (∀ τ τ' : Ω →+* Ω, spMap τ ≫ x = spMap τ' ≫ x ↔ ∀ c ∈ E, τ c = τ' c) ∧ (∀ (K' : Type) [Field K'] (j : K' →+* Ω), E ≤ j.fieldRange ↔ ∃ y : Sp K' ⟶ X, spMap j ≫ y = x) ∧ ∀ (K : Type) [Field K] [Algebra K Ω] (s : X ⟶ Sp K), LocallyOfFiniteType s → x ≫ s = spMap (algebraMap K Ω) → Algebra.IsAlgebraic K Ω → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ L.toSubfield = E := by sorry
