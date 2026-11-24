-- Prove2me | Theorems.Thm_GlobalTheory_rigidified_sym_boxLB
-- name    : GlobalTheory.rigidified_sym_boxLB
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:41.825951+00:00
-- url     : https://prove2.me/theorems/70bd5805-643b-4f43-b3b1-d2e466e5b9b9
-- title:
--   Global Theory: rigidified sym box LB
-- statement:
--   The Global Theory construction uses the rigidified sym box LB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RigidifiedSymBoxLB.lean#L86-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RigidifiedSymBoxLB.lean#L86-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedSymBoxLB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open BoxSymLoc ReciprocityTheory.ChartRestriction.G.Out.LBxP

theorem GlobalTheory.rigidified_sym_boxLB (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G']
    [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (_hL : L.IsLB) :
    (Rigidified G L → Rigidified G' (boxLB L p.pr)) ∧
      (Out.Sym G L → Out.Sym G' (boxLB L p.pr)) := by sorry
