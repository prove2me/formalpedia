-- Prove2me | Theorems.Thm_Nock_Verb_denHint_expand
-- name    : Nock.Verb.denHint_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:40.736076+00:00
-- url     : https://prove2.me/theorems/56671aa8-1951-4c46-bacb-1ffb3ce723c4
-- title:
--   Verb: den Hint expand
-- statement:
--   Hint expansion preserves `den`: `Den sub x ↔ Den e x` (OP₁₁ analogue of `den_local`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L698-L733
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L698-L733

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

theorem Nock.Verb.denHint_expand {sub e x} (he : hintExpand sub = some e) : Den sub x ↔ Den e x := by sorry
