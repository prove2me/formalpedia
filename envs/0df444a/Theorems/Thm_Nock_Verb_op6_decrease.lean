-- Prove2me | Theorems.Thm_Nock_Verb_op6_decrease
-- name    : Nock.Verb.op6_decrease
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:59.473095+00:00
-- url     : https://prove2.me/theorems/58c64599-d8cb-4cce-a998-212120dbef17
-- title:
--   Verb: op6 decrease
-- statement:
--   **OP₆ strict local decrease** (if-then-else macro).  The reduct is a 6-level nested `*`-tree;
--       its `vcost` is `SF(L,a0) + SF(c,b0) + SF([2,3],d0) + SF(L,[4[4b]])`, where the last is exactly
--       `4 + pcost g L b`, the middle two are `≤ 2` (op0), and the first is `0` or the branch cost
--       (matching the RHS branch by a full evaluation trace `b → *[L,b]∈{0,1} → +2 → slot → branch`).
--       The op₆ weight `100` dominates the macro skeleton (`8`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L219-L436
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L219-L436

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.op6_decrease {g : Nat} {L b thn els : Verb} {x : Noun} {rn2 rc : Action}
    (hL : isTerminal L = true) (htc : isTerminal (Verb.node rc thn els) = true)
    (hthn : isTerminal thn = true) (htels : isTerminal els = true)
    (hgc : denP g (Verb.node rc thn els) = some (Verb.node rc thn els).noun)
    (hdL : denP (g + 1 + 1) L = some L.noun)
    (h4b : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))
        = some (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun)))
    (ht4 : isTerminal (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) = true)
    (ht23 : isTerminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) = true)
    (hvv : evalPaper (g + 1) L.noun
        (Noun.cell (Noun.atom 6) (Verb.node rn2 b (Verb.node rc thn els)).noun) = some x) :
    vcost (g + 1 + 1)
        (Verb.node .star L
          (Verb.node .star (Verb.node rc thn els)
            (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L
                    (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))))
      < pcost (g + 1 + 1) L.noun
          (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun := by sorry
