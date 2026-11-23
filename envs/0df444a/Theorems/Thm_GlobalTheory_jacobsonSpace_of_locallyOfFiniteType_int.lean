-- Prove2me | Theorems.Thm_GlobalTheory_jacobsonSpace_of_locallyOfFiniteType_int
-- name    : GlobalTheory.jacobsonSpace_of_locallyOfFiniteType_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:07.183675+00:00
-- url     : https://prove2.me/theorems/345dedd6-e310-4d69-ac4a-173650205a37
-- title:
--   Global Theory: jacobson Space of locally Of Finite Type int
-- statement:
--   The Global Theory construction uses the jacobson Space of locally Of Finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L25-L28

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

theorem GlobalTheory.jacobsonSpace_of_locallyOfFiniteType_int {X : Scheme.{0}} (π : X ⟶ Sp ℤ)
    [LocallyOfFiniteType π] : JacobsonSpace X := by sorry
