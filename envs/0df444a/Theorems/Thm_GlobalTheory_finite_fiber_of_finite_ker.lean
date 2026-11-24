-- Prove2me | Theorems.Thm_GlobalTheory_finite_fiber_of_finite_ker
-- name    : GlobalTheory.finite_fiber_of_finite_ker
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:46:45.117714+00:00
-- url     : https://prove2.me/theorems/27fa5e6a-02f9-4761-977e-7f92fb8194c1
-- title:
--   Global Theory: finite fiber of finite ker
-- statement:
--   The Global Theory construction uses the finite fiber of finite ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LocallyQuasiFiniteOfFiniteGeometricPoints.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LocallyQuasiFiniteOfFiniteGeometricPoints.lean#L52-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LocallyQuasiFiniteOfFiniteGeometricPoints
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.finite_fiber_of_finite_ker {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Ga G T : C} [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G) [IsMonHom p]
    (h : Finite {x : T ⟶ Ga // x ≫ p = 1}) (y : T ⟶ G) :
    Finite {x : T ⟶ Ga // x ≫ p = y} := by sorry
