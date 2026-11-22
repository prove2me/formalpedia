-- Prove2me | Theorems.Thm_Nock_Verb_star_pending_is_root
-- name    : Nock.Verb.star_pending_is_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:49.753793+00:00
-- url     : https://prove2.me/theorems/4312c032-7411-49e5-9cea-339b503aac6b
-- title:
--   Verb: star pending is root
-- statement:
--   **A `*`-node with terminal children has only its root pending.**  If `map i` retrieves a
--       pending node from `*[L, R]` with `L`, `R` terminal, that node is the root itself.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L911-L921
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L911-L921

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.star_pending_is_root {L R : Verb}
    (hL : isTerminal L = true) (hR : isTerminal R = true)
    {i : Nat} {sub : Verb}
    (hmap : map i (.node .star L R) = some sub) (hp : sub.isPending = true) :
    sub = .node .star L R := by sorry
