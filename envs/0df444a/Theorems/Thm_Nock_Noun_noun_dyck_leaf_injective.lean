-- Prove2me | Theorems.Thm_Nock_Noun_noun_dyck_leaf_injective
-- name    : Nock.Noun.noun_dyck_leaf_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:27:02.464235+00:00
-- url     : https://prove2.me/theorems/fea60a32-5840-49f7-ab95-18bae24a70df
-- title:
--   Noun: noun dyck leaf injective
-- statement:
--   **Def "noun" uniqueness (main.tex:347).**  The map sending a noun to its Dyck word +
--       leaf array, `n ↦ (n.dyckWord, n.leafList)`, is injective.  This is the paper's claim
--       that the tuple `(t, dt)` "corresponds to a unique noun" (main.tex:345,347).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L272-L279
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Dyck.lean#L272-L279

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun

theorem Nock.Noun.noun_dyck_leaf_injective :
    Function.Injective (fun n : Noun => (n.dyckWord, n.leafList)) := by sorry
