-- Prove2me | Theorems.Thm_MatrixTree_det_incMat_eq_zero_of_not_injective
-- name    : MatrixTree.det_incMat_eq_zero_of_not_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T11:06:24.336503+00:00
-- url     : https://prove2.me/theorems/eee609dd-0896-4b5b-82f7-61ab7dc7d430
-- title:
--   Matrix Tree: det inc Mat eq zero of not injective
-- statement:
--   The Matrix Tree construction uses the det inc Mat eq zero of not injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L205-L209
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean#L205-L209

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem MatrixTree.det_incMat_eq_zero_of_not_injective (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ¬ Function.Injective g) : (incMat v g).det = 0 := by sorry
