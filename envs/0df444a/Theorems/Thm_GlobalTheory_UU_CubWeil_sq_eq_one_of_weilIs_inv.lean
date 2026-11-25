-- Prove2me | Theorems.Thm_GlobalTheory_UU_CubWeil_sq_eq_one_of_weilIs_inv
-- name    : GlobalTheory.UU.CubWeil.sq_eq_one_of_weilIs_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:15:32.156958+00:00
-- url     : https://prove2.me/theorems/ecb8ff91-5e00-5569-928e-f11bb6407089
-- title:
--   Cub Weil: sq eq one of weil Is inv
-- statement:
--   The Cub Weil construction uses the sq eq one of weil Is inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/NotExistsEvenTwistSymOne.lean#L177-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/NotExistsEvenTwistSymOne.lean#L177-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_NotExistsEvenTwistSymOne
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
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]

theorem GlobalTheory.UU.CubWeil.sq_eq_one_of_weilIs_inv (hG : GlobalFnsSt) (hA : IsAbelianScheme G) {L : RigLB G} {c : CubicalStr G L}
    {N : ℕ} {T : Over S} {x y : T ⟶ G} {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (h' : WeilIs G L.L N x y ζ⁻¹) :
    ζ ^ 2 = 1 := by sorry
