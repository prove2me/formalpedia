-- Prove2me | Theorems.Thm_OrderClosures_gaoIndex_approximation
-- name    : OrderClosures.gaoIndex_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:16.966562+00:00
-- url     : https://prove2.me/theorems/0556d5a0-a226-466b-a708-77ac71ee2a07
-- title:
--   Order Closures: gao Index approximation
-- statement:
--   Builds a directed family of earlier-stage indices whose projections order
--   converge to a prescribed next-stage projection.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L367-L537
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L367-L537

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gaoIndex_approximation
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) (ζ : GaoIndex ξ)
    (hζbound : ζ.1 ≤ Ordinal.omega0 ^ ξ)
    (hζleast : leastCNFExponent ζ.1 = γ) :
    ∃ Z : Set (GaoIndex ξ), Z.Nonempty ∧
      (∀ η ∈ Z, η ∈ GaoStageIndices ξ γ) ∧
      (∀ ⦃η⦄, η ∈ Z → ∀ ⦃η'⦄, η' ∈ Z →
        cnfExtensionLE η.1 η'.1 ∨ cnfExtensionLE η'.1 η.1) ∧
      IsLUB ((fun η : GaoIndex ξ ↦ η.1) '' Z) ζ.1 := by sorry
