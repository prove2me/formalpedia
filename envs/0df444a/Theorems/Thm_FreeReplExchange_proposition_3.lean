-- Prove2me | Theorems.Thm_FreeReplExchange_proposition_3
-- name    : FreeReplExchange.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:19:37.270117+00:00
-- url     : https://prove2.me/theorems/659840c3-1680-4664-9927-3de0fdb4244a
-- title:
--   Proposition 3 — at most $2\Delta-1$ nonterminal rounds under every strategy profile
-- statement:
--   Assume the sign conditions of §2.1, fix a tie order, a participating set $P$ and any strategy profile. If the initial exchange graph $G_1=G(x^{(0)},P)$ has at least one edge and maximum degree $\Delta$, then M3 has at most $2\Delta-1$ nonterminal rounds, and
--   $$\Delta\le(|P|-1)\,m,$$
--   so the number of nonterminal rounds is $O(|P|m)$. If $G_1$ has no edge, M3 has no nonterminal round.
--
--   Together with the per-round time bound this gives polynomial total running time under every strategy profile.
--
--   Differences from the source:
--   - generalization: every good is initially held by at least one agent (WLOG, p.13) → any initial allocation x⁽⁰⁾; reason: no step of the proof uses the assumption; the source's instances are among those covered
--   - generalization: a total tie order → any rank rk, not necessarily injective; reason: the proof uses only that each selected matching is maximal
--   - encoding: O(|P|m) nonterminal rounds → the explicit bound Δ ≤ (|P| − 1)m of the proof, with at most 2Δ − 1 rounds; reason: the proof derives O(|P|m) from exactly this bound
--   - generalization: the statement for a graph with at least one edge → also the edgeless case: no nonterminal round; reason: the proof's last sentence (p.39); dropping the clause gives the source's statement
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.39 (PDF p.41), Proposition 3 and its proof

import Mathlib
import Definitions.Def_FreeReplExchange_M3

namespace FreeReplExchange

/-- Proposition 3, Yang–Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.39 (PDF p.41). Suppose the initial exchange graph `G_1` has at
least one edge and has maximum degree `∆`. Under every strategy profile, M3 has at most `2∆ − 1`
nonterminal rounds. In particular, it has `O(|P|m)` nonterminal rounds.

**Formalization Note.** `O(|P|m)` is stated through the explicit bound `∆ ≤ (|P| − 1)m` of the proof
(p.39), and the proof's last sentence "If the initial graph has no edges, there are no nonterminal
rounds" is the second clause. `G_1 = G(x^(0), P)` (no rejections yet). The tie order is any rank
(only maximality of the selected matchings is used). -/
theorem proposition_3 {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (hU : SignCond U)
    (rk : Exchange A m → ℕ) (P : Finset A) (σ : A → Strategy A m) :
    ((edges x0 U P x0).Nonempty →
        nonterminalRounds (M3 x0 U rk) P σ ≤ 2 * maxDeg (edges x0 U P x0) - 1 ∧
          maxDeg (edges x0 U P x0) ≤ (P.card - 1) * m) ∧
      (edges x0 U P x0 = ∅ → nonterminalRounds (M3 x0 U rk) P σ = 0) := by sorry

end FreeReplExchange
