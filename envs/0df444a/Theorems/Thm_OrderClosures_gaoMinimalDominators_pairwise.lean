-- Prove2me | Theorems.Thm_OrderClosures_gaoMinimalDominators_pairwise
-- name    : OrderClosures.gaoMinimalDominators_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:07.604493+00:00
-- url     : https://prove2.me/theorems/cddb00bc-e7f0-4865-89a5-518a14a9eaaa
-- title:
--   Order Closures: gao Minimal Dominators pairwise
-- statement:
--   Shows that distinct minimal dominators are CNF-incomparable; used with the
--   incomparable-projection infimum theorem.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L70-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L70-L75

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gaoMinimalDominators_pairwise
    (ξ γ : Ordinal.{u}) (b : C(GaoCompactSpace ξ, ℝ)) :
    (gaoMinimalDominators ξ γ b).Pairwise
      (fun μ ν ↦ ¬ cnfExtensionLE μ.1 ν.1) := by sorry
