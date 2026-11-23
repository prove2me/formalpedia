-- Prove2me | Theorems.Thm_GlobalTheory_FibreLinInd_exists_lift
-- name    : GlobalTheory.FibreLinInd.exists_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:28.114678+00:00
-- url     : https://prove2.me/theorems/069b7427-73d2-4b0f-9b27-84a1d07bbce8
-- title:
--   Fibre Lin Ind: exists lift
-- statement:
--   The Fibre Lin Ind construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L66-L75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres
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
noncomputable section
open GlobalTheory GlobalTheory.FibreLinInd

theorem GlobalTheory.FibreLinInd.exists_lift {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) (w : W) (t : Sp K) (hw : q w = x t) :
    ∃ h : Sp K ⟶ W, h ≫ q = x := by sorry
