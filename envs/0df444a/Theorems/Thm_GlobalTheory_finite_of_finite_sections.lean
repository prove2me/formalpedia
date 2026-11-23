-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_finite_sections
-- name    : GlobalTheory.finite_of_finite_sections
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:20.542869+00:00
-- url     : https://prove2.me/theorems/bda777d3-58cd-4468-90f6-fc25d6b459a2
-- title:
--   Global Theory: finite of finite sections
-- statement:
--   The Global Theory construction uses the finite of finite sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LocallyQuasiFiniteOfFiniteGeometricPoints.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LocallyQuasiFiniteOfFiniteGeometricPoints.lean#L10-L23

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

theorem GlobalTheory.finite_of_finite_sections {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P : Scheme.{0}}
    (s : P ⟶ Spec (.of Ω)) [LocallyOfFiniteType s]
    (h : Finite {x : Spec (.of Ω) ⟶ P // x ≫ s = 𝟙 _}) : Finite P := by sorry
