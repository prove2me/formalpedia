-- Prove2me | Theorems.Thm_IsSigmaOrderContinuousNorm_tendsto_of_antitone_isGLB
-- name    : IsSigmaOrderContinuousNorm.tendsto_of_antitone_isGLB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:00.257573+00:00
-- url     : https://prove2.me/theorems/e9295738-2629-47b4-abc1-ee5ce6b885d6
-- title:
--   Is Sigma Order Continuous Norm: tendsto of antitone is GLB
-- statement:
--   An antitone sequence with a greatest lower bound converges in norm to
--   that bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Basic.lean#L147-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Basic.lean#L147-L166

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

theorem IsSigmaOrderContinuousNorm.tendsto_of_antitone_isGLB {u : ℕ → X} {x : X}
    (hanti : Antitone u) (hglb : IsGLB (Set.range u) x) :
    Filter.Tendsto u Filter.atTop (nhds x) := by sorry
