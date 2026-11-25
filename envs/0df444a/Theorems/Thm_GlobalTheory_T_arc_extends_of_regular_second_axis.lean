-- Prove2me | Theorems.Thm_GlobalTheory_T_arc_extends_of_regular_second_axis
-- name    : GlobalTheory.T.arc_extends_of_regular_second_axis
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:47.013714+00:00
-- url     : https://prove2.me/theorems/f26b44c6-2c5c-4830-a375-2a463ec3baa7
-- title:
--   T: arc extends of regular second axis
-- statement:
--   The T construction uses the arc extends of regular second axis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ArcExtendsOfRegularSecondAxisStatement.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ArcExtendsOfRegularSecondAxisStatement.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ArcExtendsOfRegularSecondAxis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ArcExtendsOfRegularSecondAxisStatement
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
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.arc_extends_of_regular_second_axis : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ (a : algOver k (FractionRing (PowerSeries k)) ⟶ G) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → TwoVar j f a h d → (∀ i, ∃ u v, ¬ MvPowerSeries.X 1 ∣ v ∧ h i * v = d * u) → ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (IsScalarTower.toAlgHom k (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a := by sorry
