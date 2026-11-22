-- Prove2me | Theorems.Thm_Nock_Verb_op6_decreaseN
-- name    : Nock.Verb.op6_decreaseN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:16:07.587316+00:00
-- url     : https://prove2.me/theorems/d69e6cda-d9ba-45c3-8b28-d091208e11a5
-- title:
--   Verb: op6 decrease N
-- statement:
--   The Verb construction uses the op6 decrease N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L432-L632
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L432-L632

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.op6_decreaseN {g : Nat} {L b thn els : Verb} {x : Noun} {rn2 rc : Action}
    (hL : isTerminal L = true) (htc : isTerminal (Verb.node rc thn els) = true)
    (hthn : isTerminal thn = true) (htels : isTerminal els = true)
    (hgc : den g (Verb.node rc thn els) = some (Verb.node rc thn els).noun)
    (hdL : den (g + 1 + 1) L = some L.noun)
    (h4b : den (g + 1 + 1) (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))
        = some (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun)))
    (ht4 : isTerminal (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) = true)
    (ht23 : isTerminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) = true)
    (hvv : evalN (g + 1) L.noun
        (Noun.cell (Noun.atom 6) (Verb.node rn2 b (Verb.node rc thn els)).noun) = some x) :
    vcostN (g + 1 + 1)
        (Verb.node .star L
          (Verb.node .star (Verb.node rc thn els)
            (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L
                    (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))))
      < ncost (g + 1 + 1) L.noun
          (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun := by sorry
