-- Prove2me | Theorems.Thm_FreeReplExchange_theorem_11
-- name    : FreeReplExchange.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:18:43.425994+00:00
-- url     : https://prove2.me/theorems/11a4017e-5bf8-4093-b115-39855d8f68ca
-- title:
--   Theorem 11 — matching correspondence
-- statement:
--   Assume the sign conditions of §2.1, and let $x\ge x^{(0)}$ and $P$ be a participating set.
--
--   1. A set $\mathcal P$ of well-formed proposals among $P$ is MIC with respect to $x$ if and only if, after omitting the exchanges $p$ with $x[\{p\}]=x$, the remaining exchanges form a matching in the exchange graph $G(x,P)$.
--   2. Under the accepting strategy profile, the exchanges of a matching $\mu$ of $G(x,P)$ fill exactly $2|\mu|$ empty slots:
--   $$\sum_{k,q}x[\mu]_{k,q}=\sum_{k,q}x_{k,q}+2|\mu| .$$
--
--   Maximizing the number of slots filled in one MIC round therefore reduces to a maximum matching problem.
--
--   Differences from the source:
--   - generalization: every good is initially held by at least one agent (WLOG, p.13) → any initial allocation x⁽⁰⁾; reason: no step of the proof uses the assumption; the source's instances are among those covered
--   - encoding: fills exactly 2|μ| empty slots → the filled-slot count after executing μ with all decisions accept equals the count before plus 2|μ|; reason: filled slots stay filled, so the two say the same
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.31 (PDF p.33), Theorem 11

import Mathlib
import Definitions.Def_FreeReplExchange_IsMICSet
import Definitions.Def_FreeReplExchange_m3Select

namespace FreeReplExchange

open Classical in
/-- Theorem 11 (Matching correspondence), Yang–Kandasamy, *Pairwise Exchanges of Freely Replicable
Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.31 (PDF p.33). A set of exchanges is MIC
with respect to `x` iff, after omitting exchanges that leave holdings unchanged, the remaining
exchanges correspond to a matching in `G(x, P)`. Under the accepting strategy profile, a set of
exchanges corresponding to a matching `μ` fills exactly `2|μ|` empty slots.

**Formalization Note.** A matching of `G(x, P)` is a subset of the edge set (15) whose edges have
pairwise disjoint endpoints (`matchingsOf`), edges being identified with exchanges. As in
Desideratum 3 the set consists of well-formed proposals among `P` and `x ≥ x^(0)`; the sign
conditions of §2.1 are standing. "Fills exactly `2|μ|` empty slots" is the filled-slot count
after executing `μ` with every decision an acceptance. -/
theorem theorem_11 {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (hU : SignCond U) (P : Finset A)
    (x : A → Fin m → Bool) (hx : Dominates x0 x) :
    (∀ Props : Finset (Exchange A m), (∀ p ∈ Props, WellFormed x0 P p) →
      (IsMICSet U P x Props ↔
        Props.filter (fun p => exec x {p} ≠ x) ∈ matchingsOf (edges x0 U P x))) ∧
    (∀ μ ∈ matchingsOf (edges x0 U P x),
      filledCount (outcome x μ fun _ _ => true) = filledCount x + 2 * μ.card) := by sorry

end FreeReplExchange
