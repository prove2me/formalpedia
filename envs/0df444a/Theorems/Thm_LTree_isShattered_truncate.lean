-- Prove2me | Theorems.Thm_LTree_isShattered_truncate
-- name    : LTree.isShattered_truncate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:16.339382+00:00
-- url     : https://prove2.me/theorems/10ea51a5-ffb0-4844-82cd-287a12795ced
-- title:
--   LTree: is Shattered truncate
-- statement:
--   A truncated tree is shattered if the original is.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean#L116-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Online.lean#L116-L128

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
set_option autoImplicit true
@[expose] public section
public section

theorem LTree.isShattered_truncate {X : Type} {C : ConceptClass X Bool}
    {m : ℕ} (T : LTree X m) (hT : T.isShattered C) {n : ℕ} (h : n ≤ m) :
    (T.truncate h).isShattered C := by sorry
