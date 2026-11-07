-- Prove2me | Theorems.Thm_HalfIndMatch_greedy_maximal
-- name    : HalfIndMatch.greedy_maximal
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:13:10.298658+00:00
-- url     : https://prove2.me/theorems/2009d96f-6613-4c38-b342-c9a15500cb62
-- title:
--   §3.1, pp.12–13 — the output $M_n$ of Greedy is a maximal induced matching
-- statement:
--   Let $G$ be any graph on $[n]$. For every ordering of the vertices and every way of choosing the vertices $u_t$, the output $M_n$ of the Greedy algorithm (Algorithm 3.1) is a **maximal induced matching** of $G$: it is an induced matching, and no edge of $G$ can be added to it while keeping it induced.
--
--   This deterministic fact is what lets Theorem 2.1 follow from Proposition 3.1, which bounds the size of every maximal induced matching of $G(n,p)$.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - generalization: one fixed arbitrary ordering 1, …, n and an arbitrary choice of each u_t → every vertex order σ (a permutation of Fin n) and every choice rule pick; reason: the source's run is one of these runs for any graph, so the statement specializes to it
--   - encoding: choose an arbitrary u_t ∈ N(t) ∩ B_{t−1} → u_t = pick t (N(t) ∩ B_{t−1}) if it is a candidate, else the least candidate; reason: every choice sequence is realized by some pick; the run is total
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), §3.1, the claim after Algorithm 3.1, pp.12–13 (PDF pp.14–15)

import Mathlib
import Definitions.Def_HalfIndMatch_IsInducedMatching
import Definitions.Def_HalfIndMatch_greedyOut

namespace HalfIndMatch

/-- §3.1, pp.12–13: for every graph `G` on `Fin n`, every vertex order `σ` and every choice rule
`pick`, the output `M_n` of Greedy is a maximal induced matching of `G`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), §3.1, the claim after Algorithm 3.1, pp.12–13 (PDF pp.14–15).

**Formalization Note** Deterministic, for every graph. The order and the choice rule are
universally quantified (see `greedyOut`). -/
theorem greedy_maximal {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    (pick : ℕ → Finset (Fin n) → Fin n) :
    IsMaximalInducedMatching G (greedyOut G σ pick) := by sorry

end HalfIndMatch
