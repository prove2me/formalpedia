-- Prove2me | Theorems.Thm_GlobalTheory_subset_of_isOpen_of_closedPoints
-- name    : GlobalTheory.subset_of_isOpen_of_closedPoints
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:21.297598+00:00
-- url     : https://prove2.me/theorems/a4c5a155-bc7d-488e-baad-909c9252113e
-- title:
--   Global Theory: subset of is Open of closed Points
-- statement:
--   The Global Theory construction uses the subset of is Open of closed Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp.lean#L46-L52

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
variable {T : Type*} [TopologicalSpace T] [JacobsonSpace T]

theorem GlobalTheory.subset_of_isOpen_of_closedPoints {U V : Set T} (hU : IsOpen U) (hV : IsOpen V)
    (h : ∀ x, IsClosed ({x} : Set T) → x ∈ U → x ∈ V) : U ⊆ V := by sorry
