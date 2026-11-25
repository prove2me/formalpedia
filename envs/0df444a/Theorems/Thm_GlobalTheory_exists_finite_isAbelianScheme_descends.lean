-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_isAbelianScheme_descends
-- name    : GlobalTheory.exists_finite_isAbelianScheme_descends
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:56:57.409443+00:00
-- url     : https://prove2.me/theorems/c1cba0c0-cd56-5871-a1a4-c95a5fa927c9
-- title:
--   Global Theory: exists finite is Abelian Scheme descends
-- statement:
--   The Global Theory construction uses the exists finite is Abelian Scheme descends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteIsAbelianSchemeDescends.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteIsAbelianSchemeDescends.lean#L49-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteIsAbelianSchemeDescends
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS GlobalTheory.FieldModel
open GlobalTheory

theorem GlobalTheory.exists_finite_isAbelianScheme_descends : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (B : Over (Sp Ω)) [GrpObj B], IsAbelianScheme B → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (B₁ : Over (Sp L)) (_ : GrpObj B₁) (e : (Over.pullback (spMap (algebraMap L Ω))).obj B₁ ≅ B), IsAbelianScheme B₁ ∧ IsMonHom e.hom := by sorry
