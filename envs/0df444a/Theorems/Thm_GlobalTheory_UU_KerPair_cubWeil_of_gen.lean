-- Prove2me | Theorems.Thm_GlobalTheory_UU_KerPair_cubWeil_of_gen
-- name    : GlobalTheory.UU.KerPair.cubWeil_of_gen
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:22.104395+00:00
-- url     : https://prove2.me/theorems/c96756e4-0f29-4cea-b78b-9c85a3b326fd
-- title:
--   Ker Pair: cub Weil of gen
-- statement:
--   The Ker Pair construction uses the cub Weil of gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubWeilOfGen.lean#L156-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubWeilOfGen.lean#L156-L182

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
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B} (c : CubicalStr B L)
  {T : Over S} {x : T ⟶ B}

theorem GlobalTheory.UU.KerPair.cubWeil_of_gen : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ) (T : Over S) (x y : T ⟶ B), x ^ N = 1 → y ^ N = 1 → (∃ u : LB.Gen (translDiff B L.L x), u.IsGen) → CubWeil c N x y 1) := by sorry
