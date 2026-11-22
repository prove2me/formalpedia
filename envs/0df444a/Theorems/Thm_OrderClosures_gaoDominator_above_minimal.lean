-- Prove2me | Theorems.Thm_OrderClosures_gaoDominator_above_minimal
-- name    : OrderClosures.gaoDominator_above_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:02.920221+00:00
-- url     : https://prove2.me/theorems/2c47907c-cd5a-4b93-b9a9-fec22347b698
-- title:
--   Order Closures: gao Dominator above minimal
-- statement:
--   Refines any dominator to a minimal one; used to replace arbitrary
--   dominating coordinates by a finite canonical family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L51-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L51-L66

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gaoDominator_above_minimal
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    {ζ : GaoIndex ξ} (hζ : ζ ∈ gaoDominators ξ γ b) :
    ∃ μ ∈ gaoMinimalDominators ξ γ b, cnfExtensionLE μ.1 ζ.1 := by sorry
