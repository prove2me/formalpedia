-- Prove2me | Theorems.Thm_GlobalTheory_SS_exists_fieldOfValues
-- name    : GlobalTheory.SS.exists_fieldOfValues
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:49.842788+00:00
-- url     : https://prove2.me/theorems/e0ca544d-08c6-42fb-916a-524d48250c71
-- title:
--   SS: exists field Of Values
-- statement:
--   The SS construction uses the exists field Of Values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFieldOfValues.lean#L42-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFieldOfValues.lean#L42-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfValues
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
open GlobalTheory GlobalTheory.SS

theorem GlobalTheory.SS.exists_fieldOfValues : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X), ∃ E : Subfield Ω, (∀ τ τ' : Ω →+* Ω, spMap τ ≫ x = spMap τ' ≫ x ↔ ∀ c ∈ E, τ c = τ' c) ∧ (∀ (K' : Type) [Field K'] (j : K' →+* Ω), E ≤ j.fieldRange ↔ ∃ y : Sp K' ⟶ X, spMap j ≫ y = x) ∧ ∀ (K : Type) [Field K] [Algebra K Ω] (s : X ⟶ Sp K), LocallyOfFiniteType s → x ≫ s = spMap (algebraMap K Ω) → Algebra.IsAlgebraic K Ω → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ L.toSubfield = E := by sorry
