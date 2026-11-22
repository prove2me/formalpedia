-- Prove2me | Theorems.Thm_IsSigmaOrderContinuousNorm_tendsto_norm_of_monotone_isLUB
-- name    : IsSigmaOrderContinuousNorm.tendsto_norm_of_monotone_isLUB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:51.092807+00:00
-- url     : https://prove2.me/theorems/0b18e371-1f9a-4b78-a841-350de14bd877
-- title:
--   Is Sigma Order Continuous Norm: tendsto norm of monotone is LUB
-- statement:
--   The norm itself is an order continuous function on positive elements:
--   if `u n` converges in order to `x`, then `‖u n‖ → ‖x‖`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Basic.lean#L185-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Basic.lean#L185-L189

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

theorem IsSigmaOrderContinuousNorm.tendsto_norm_of_monotone_isLUB {u : ℕ → X} {x : X}
    (hmono : Monotone u)
    (hlub : IsLUB (Set.range u) x) :
    Filter.Tendsto (fun n => ‖u n‖) Filter.atTop (nhds ‖x‖) := by sorry
