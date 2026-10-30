-- Prove2me | Theorems.Thm_HofmannStreicher1994_substitution_locality
-- name    : HofmannStreicher1994.substitution_locality
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T01:51:00.002876+00:00
-- url     : https://prove2.me/theorems/08b4286b-4461-4cfd-918e-e29375a8c600
-- title:
--   Substitution locality for well-typed expressions
-- statement:
--   Let $\Gamma$ be a finite context, and let $e$ be either a type well formed in $\Gamma$ or a term well typed in $\Gamma$. Let $\sigma$ and $\tau$ be arbitrary simultaneous substitutions. If they agree at every variable index belonging to the context, then
--
--   $$e[\sigma]=e[\tau].$$
--
--   The equality is literal equality of the resulting raw expressions. No typing condition is required of the replacement expressions. This permits a substitution to be truncated outside the context when proving semantic substitution and soundness.
--
--   This is an auxiliary structural lemma for the mission's fixed object syntax; it does not assert semantic soundness or UIP independence.
-- source:
--   Auxiliary lemma derived from the mission's fixed definition module Definitions.Def_HofmannStreicher1994_Syntax: Expr, substitute, TypeWf, TermWf, and the mutually inductive judgments. Mission 6dee1b1f-e7c2-4269-818b-ea9047240380, supporting HofmannStreicher1994.uip_underivable. This structural lemma is not claimed to be a separately numbered result in the 1994 paper.

import Definitions.Def_HofmannStreicher1994_Syntax
open HofmannStreicher1994

theorem HofmannStreicher1994.substitution_locality
    (Γ : Context) (e : Expr) (σ τ : Nat → Expr)
    (h : TypeWf Γ e ∨ ∃ A, TermWf Γ e A)
    (hστ : ∀ n, n < Γ.length → σ n = τ n) :
    substitute σ e = substitute τ e := by sorry
