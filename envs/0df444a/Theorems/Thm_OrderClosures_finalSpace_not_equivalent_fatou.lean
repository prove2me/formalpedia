-- Prove2me | Theorems.Thm_OrderClosures_finalSpace_not_equivalent_fatou
-- name    : OrderClosures.finalSpace_not_equivalent_fatou
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:31.341039+00:00
-- url     : https://prove2.me/theorems/56d92b73-5137-41a1-8e9d-f32316a96958
-- title:
--   Order Closures: final Space not equivalent fatou
-- statement:
--   The constructed `c₀`-sum admits no equivalent Fatou lattice norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L540-L585
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/FinalSpace.lean#L540-L585

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.finalSpace_not_equivalent_fatou :
    ∀ q : PaperLatticeNorm FinalSpace,
      HasFatouProperty q → ¬ EquivalentNorms finalLatticeNorm q := by sorry
