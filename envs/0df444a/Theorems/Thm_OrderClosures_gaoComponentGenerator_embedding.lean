-- Prove2me | Theorems.Thm_OrderClosures_gaoComponentGenerator_embedding
-- name    : OrderClosures.gaoComponentGenerator_embedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:00.578198+00:00
-- url     : https://prove2.me/theorems/2dd0176a-49f6-40f6-8a94-d6ac9a28047c
-- title:
--   Order Closures: gao Component Generator embedding
-- statement:
--   Evaluates a component generator after embedding into the padded product;
--   used to relate global generators to their Gao coordinates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L160-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L160-L173

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gaoComponentGenerator_embedding
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) (ζ : GaoSuccessorGenerator β.1) :
    gaoComponentGenerator κ hκ β
        (gaoGeneratorEmbedding κ hκ β.1 β.2 ζ) =
      ordinalProjection β.1 ζ.1 := by sorry
