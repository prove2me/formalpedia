-- Prove2me | Theorems.Thm_GlobalTheory_finite_field_of_finiteType_int
-- name    : GlobalTheory.finite_field_of_finiteType_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:07.905519+00:00
-- url     : https://prove2.me/theorems/472d5d10-6feb-4699-b4b7-eede29ac716e
-- title:
--   Global Theory: finite field of finite Type int
-- statement:
--   The Global Theory construction uses the finite field of finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L10-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.finite_field_of_finiteType_int (K : Type*) [Field K] [Algebra.FiniteType ℤ K] :
    Finite K := by sorry
