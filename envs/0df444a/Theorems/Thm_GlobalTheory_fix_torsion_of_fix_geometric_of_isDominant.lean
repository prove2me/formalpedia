-- Prove2me | Theorems.Thm_GlobalTheory_fix_torsion_of_fix_geometric_of_isDominant
-- name    : GlobalTheory.fix_torsion_of_fix_geometric_of_isDominant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:27.5217+00:00
-- url     : https://prove2.me/theorems/1793e539-606c-4824-ba3e-f7324015ec9f
-- title:
--   Global Theory: fix torsion of fix geometric of is Dominant
-- statement:
--   The Global Theory construction uses the fix torsion of fix geometric of is Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqOfDominantGeometricPointsOfUnramified.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqOfDominantGeometricPointsOfUnramified.lean#L103-L111

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

theorem GlobalTheory.fix_torsion_of_fix_geometric_of_isDominant (hmul : MulNSt) {S : Scheme.{0}}
    [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (hM : 1 ≤ M) (hMu : IsUnit (M : Γ(S, ⊤)))
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : P.A ⟶ P.A) (hsm : IsMonHom s)
    (hs : ∀ x : Over.mk t ⟶ P.A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ P.A) (hx : x ^ M = 1) : x ≫ s = x := by sorry
