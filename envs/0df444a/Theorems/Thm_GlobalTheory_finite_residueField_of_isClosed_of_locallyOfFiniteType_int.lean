-- Prove2me | Theorems.Thm_GlobalTheory_finite_residueField_of_isClosed_of_locallyOfFiniteType_int
-- name    : GlobalTheory.finite_residueField_of_isClosed_of_locallyOfFiniteType_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:27.089807+00:00
-- url     : https://prove2.me/theorems/fe0bc00f-2d72-45a6-890f-471859fdc16a
-- title:
--   Global Theory: finite residue Field of is Closed of locally Of Finite Type int
-- statement:
--   The Global Theory construction uses the finite residue Field of is Closed of locally Of Finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L30-L40

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

theorem GlobalTheory.finite_residueField_of_isClosed_of_locallyOfFiniteType_int {X : Scheme.{0}}
    (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : X) (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by sorry
