-- Prove2me | Theorems.Thm_FreeReplExchange_proposition_2
-- name    : FreeReplExchange.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:19:32.187067+00:00
-- url     : https://prove2.me/theorems/ca1f24ea-83cd-4c71-8323-1159bf311f2c
-- title:
--   Proposition 2 — M3 is MIC, stable and efficient for general utilities
-- statement:
--   Assume the sign conditions of §2.1. For every global tie order, the protocol M3 satisfies MIC and stability under every strategy profile and every participating set, and efficiency under the accepting strategy profile. Moreover, under every participating set and strategy profile, M3 terminates after finitely many rounds (by the horizon at which terminal outcomes are read).
--
--   These are the guarantees of item 1 of Theorem 10.
--
--   Differences from the source:
--   - generalization: every good is initially held by at least one agent (WLOG, p.13) → any initial allocation x⁽⁰⁾; reason: no step of the proof uses the assumption; the source's instances are among those covered
--   - generalization: a total order e₁ ≺ ⋯ ≺ e_L on all potential exchanges (p.32) → any rank rk : Exchange → ℕ, not necessarily injective; reason: the proof uses only the maximum-cardinality objective (p.34: "These three guarantees use only the maximum-cardinality objective"); total orders are the injective ranks
--   - encoding: the run until termination and its terminal allocation x⁽∞⁾ and rejected set D_∞ (p.14) → the run read at the horizon L = number of quadruples ((i,r),(j,s)), with a conjunct that the protocol has posted the empty set by then; reason: each nonterminal round removes at least one edge, so the conjunct makes the history at the horizon the terminal one
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.34 (PDF p.36), Proposition 2 and its proof

import Mathlib
import Definitions.Def_FreeReplExchange_IsEfficient
import Definitions.Def_FreeReplExchange_M3

namespace FreeReplExchange

/-- Proposition 2, Yang–Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.34 (PDF p.36). For general utility matrices, M3 satisfies MIC
and stability under every strategy profile, and efficiency under the accepting strategy profile.

**Formalization Note.** The first conjunct is the proof's "Thus the protocol terminates after
finitely many rounds": under every participating set and profile the run has stopped by the
horizon at which `x^(∞)` and `D_∞` are read. The tie order is any rank `rk`, not necessarily
injective (the paper: "These three guarantees use only the maximum-cardinality objective"). -/
theorem proposition_2 {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (hU : SignCond U)
    (rk : Exchange A m → ℕ) :
    TerminatesByHorizon (M3 x0 U rk) ∧ IsMIC x0 U (M3 x0 U rk) ∧ IsStable x0 U (M3 x0 U rk) ∧
      IsEfficient x0 U (M3 x0 U rk) := by sorry

end FreeReplExchange
