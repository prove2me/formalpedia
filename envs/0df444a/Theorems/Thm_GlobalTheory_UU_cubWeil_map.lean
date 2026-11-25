-- Prove2me | Theorems.Thm_GlobalTheory_UU_cubWeil_map
-- name    : GlobalTheory.UU.cubWeil_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:59:46.169348+00:00
-- url     : https://prove2.me/theorems/73a585b9-356b-483f-90a3-5bf9d7ef1f92
-- title:
--   UU: cub Weil map
-- statement:
--   The UU construction uses the cub Weil map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubNRatioTwist.lean#L75-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubNRatioTwist.lean#L75-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubNRatioTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.UU

theorem GlobalTheory.UU.cubWeil_map : (∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (P : CP G) (P' : CP G') (F : G'.left ⟶ G.left) (hw) (w), IsCPMap P' P f F hw w → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil P'.c N x y ζ → CubWeil P.c N (toBase hw x) (toBase hw y) ζ) := by sorry
