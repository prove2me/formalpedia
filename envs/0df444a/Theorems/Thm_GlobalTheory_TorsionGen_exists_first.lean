-- Prove2me | Theorems.Thm_GlobalTheory_TorsionGen_exists_first
-- name    : GlobalTheory.TorsionGen.exists_first
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T17:13:27.332802+00:00
-- url     : https://prove2.me/theorems/907587aa-3ba5-5e28-a8f5-ee57c12558b4
-- title:
--   Torsion Gen: exists first
-- statement:
--   The Torsion Gen construction uses the exists first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdCocycleMul.lean#L156-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdCocycleMul.lean#L156-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdCocycleMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionGen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)

theorem GlobalTheory.TorsionGen.exists_first {T : Over S} (x a : T ⟶ G) (n : ℕ) :
    ∃ t : LB.Gen (LB.LinComb P (K := Fin 3) ![(lift (x ^ n) a).left, (lift (x ^ 0) a).left, (lift x a).left] ![1, -1, -n]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J → val t ρ.left z J =
        ∏ k ∈ Finset.range n, val β.law1 (lift ((ρ ≫ x) ^ k) (lift (ρ ≫ x) (ρ ≫ a))).left z J := by sorry
