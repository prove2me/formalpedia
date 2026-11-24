-- Prove2me | Theorems.Thm_GlobalTheory_fix_torsion_of_fix_geometric_of_etale
-- name    : GlobalTheory.fix_torsion_of_fix_geometric_of_etale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:12.92566+00:00
-- url     : https://prove2.me/theorems/91096179-6916-47f7-950b-b00032d27a31
-- title:
--   Global Theory: fix torsion of fix geometric of etale
-- statement:
--   The Global Theory construction uses the fix torsion of fix geometric of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqOfDominantGeometricPointsOfUnramified.lean#L52-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqOfDominantGeometricPointsOfUnramified.lean#L52-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqOfDominantGeometricPointsOfUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
universe u
open GlobalTheory

theorem GlobalTheory.fix_torsion_of_fix_geometric_of_etale {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : ℕ)
    [Etale (mulA A M).left] [IsSeparated (mulA A M).left]
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : A ⟶ A) [IsMonHom s]
    (hs : ∀ x : Over.mk t ⟶ A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ A) (hx : x ^ M = 1) : x ≫ s = x := by sorry
