-- Prove2me | Theorems.Thm_GlobalTheory_UU_KerPair_exists_pow_gen
-- name    : GlobalTheory.UU.KerPair.exists_pow_gen
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:13:47.803914+00:00
-- url     : https://prove2.me/theorems/7c6204a2-9fee-5558-9156-d7b61bf39858
-- title:
--   Ker Pair: exists pow gen
-- statement:
--   The Ker Pair construction uses the exists pow gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubWeilOfGen.lean#L21-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubWeilOfGen.lean#L21-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOfGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.KerPair

theorem GlobalTheory.UU.KerPair.exists_pow_gen {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by sorry
