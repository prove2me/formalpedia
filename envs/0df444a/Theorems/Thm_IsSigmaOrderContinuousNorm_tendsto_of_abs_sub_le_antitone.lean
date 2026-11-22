-- Prove2me | Theorems.Thm_IsSigmaOrderContinuousNorm_tendsto_of_abs_sub_le_antitone
-- name    : IsSigmaOrderContinuousNorm.tendsto_of_abs_sub_le_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:57.883051+00:00
-- url     : https://prove2.me/theorems/15a8a83c-bcf2-45e4-9d69-7ec0f429c38f
-- title:
--   Is Sigma Order Continuous Norm: tendsto of abs sub le antitone
-- statement:
--   The norm is σ-order continuous: if `|u n - x| ≤ v n` for an antitone
--   sequence `v` with `inf v = 0`, then `u n → x` in norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Basic.lean#L170-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Basic.lean#L170-L181

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
set_option autoImplicit true
@[expose] public section
public section
universe u
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open IsSigmaOrderContinuousNorm
variable [NormedVectorLattice X] [IsSigmaOrderContinuousNorm X]

theorem IsSigmaOrderContinuousNorm.tendsto_of_abs_sub_le_antitone {u : ℕ → X} {v : ℕ → X} {x : X}
    (hv_anti : Antitone v) (hv_nn : ∀ n, 0 ≤ v n)
    (hv_glb : IsGLB (Set.range v) 0)
    (hle : ∀ n, |u n - x| ≤ v n) :
    Filter.Tendsto u Filter.atTop (nhds x) := by sorry
