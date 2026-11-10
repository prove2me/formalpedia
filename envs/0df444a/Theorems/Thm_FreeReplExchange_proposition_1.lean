-- Prove2me | Theorems.Thm_FreeReplExchange_proposition_1
-- name    : FreeReplExchange.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:18:36.192849+00:00
-- url     : https://prove2.me/theorems/98832772-37db-470f-8420-447fdc211cea
-- title:
--   Proposition 1 — MIC characterizes the proposable sets
-- statement:
--   Assume the sign conditions $(U_i)_{i,r}\in(0,1]$, $(U_i)_{j,r}\in[-1,0)$ ($j\ne i$). Let $P$ be a participating set, $x\ge x^{(0)}$ an allocation and $\mathcal P$ a set of well-formed proposals among $P$ with $x[\{p\}]\neq x$ for every $p\in\mathcal P$. Then $\mathcal P$ is MIC with respect to $x$ if and only if
--
--   1. every $p\in\mathcal P$ is mutually beneficial at $x$, and
--   2. $R(p)\cap R(q)=\varnothing$ for every distinct $p,q\in\mathcal P$.
--
--   This identifies the sets a MIC protocol may post and underlies the matching correspondence of Theorem 11.
--
--   Differences from the source:
--   - generalization: every good is initially held by at least one agent (WLOG, p.13) → any initial allocation x⁽⁰⁾; reason: no step of the proof uses the assumption; the source's instances are among those covered
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.16 (PDF p.18), Proposition 1

import Mathlib
import Definitions.Def_FreeReplExchange_feasible
import Definitions.Def_FreeReplExchange_IsMICSet

namespace FreeReplExchange

/-- Proposition 1 (MIC characterizes the proposable sets), Yang–Kandasamy, *Pairwise Exchanges of
Freely Replicable Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.16 (PDF p.18). Let
`Props` be a set of well-formed proposals among `P` with `x[{p}] ≠ x` for every `p ∈ Props`. Then
`Props` is MIC with respect to `x` iff (i) every `p ∈ Props` is mutually beneficial at `x` and
(ii) `R(p) ∩ R(q) = ∅` for every distinct `p, q ∈ Props`.

**Formalization Note.** The standing assumptions are the sign conditions of §2.1 and, from
Desideratum 3, `x ≥ x^(0)` and well-formedness of the proposals among `P`. MIC is the
game-theoretic (7). -/
theorem proposition_1 {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (hU : SignCond U) (P : Finset A)
    (x : A → Fin m → Bool) (hx : Dominates x0 x) (Props : Finset (Exchange A m))
    (hwf : ∀ p ∈ Props, WellFormed x0 P p) (hch : ∀ p ∈ Props, exec x {p} ≠ x) :
    IsMICSet U P x Props ↔ (∀ p ∈ Props, MutBen U x p) ∧ RecvDisjoint Props := by sorry

end FreeReplExchange
