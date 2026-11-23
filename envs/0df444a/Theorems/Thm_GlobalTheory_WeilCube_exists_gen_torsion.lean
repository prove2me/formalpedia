-- Prove2me | Theorems.Thm_GlobalTheory_WeilCube_exists_gen_torsion
-- name    : GlobalTheory.WeilCube.exists_gen_torsion
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:12.145362+00:00
-- url     : https://prove2.me/theorems/db2bd8cb-4a62-4b97-98b2-2d361a2f0fce
-- title:
--   Weil Cube: exists gen torsion
-- statement:
--   The Weil Cube construction uses the exists gen torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean#L35-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory.WeilCube
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)

theorem GlobalTheory.WeilCube.exists_gen_torsion {T : Over S} (k : ℕ) (x y : T ⟶ A) (hx : x ^ k = 1) :
    ∃ t : LB.Gen (LB.LinComb Lr.L (K := Fin 4) ![(x * y).left, x.left, y.left, (1 : T ⟶ A).left] ![-k, k, k, -k]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good Lr.L z J →
        val t ρ.left z J = cubN (cubV c z J) k 1 (ρ ≫ x) (ρ ≫ y) := by sorry
