-- Prove2me | Theorems.Thm_HalfIndMatch_theorem_2_1
-- name    : HalfIndMatch.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:14:09.416735+00:00
-- url     : https://prove2.me/theorems/b9a133bb-4937-47f6-b9d7-444c9dcb1193
-- title:
--   Theorem 2.1 — Greedy finds an induced matching of size $\ge(1/2-\varepsilon)L$ with probability $\ge1-e^{-n^\varepsilon}$
-- statement:
--   Fix $\kappa\in(0,1)$ and $\varepsilon\in(0,1/2)$, and let $L$ be given by (1). There is a constant $C=C(\varepsilon,\kappa)>0$ such that, for all sufficiently large $n$ and all $C/n\le p\le1-\kappa$, the output $M_n$ of Greedy on $G\sim G(n,p)$ satisfies
--
--   $$\mathbb P\Big[|M_n|\ge\Big(\tfrac12-\varepsilon\Big)L\Big]\ge1-\exp(-n^{\varepsilon}).$$
--
--   The event is taken in the strong form "for every vertex order and every choice of the $u_t$, the Greedy output has at least $(1/2-\varepsilon)L$ edges". Together with Theorem 2.3 it shows that $(1/2+o(1))L$ is the optimal size attainable online.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - encoding: G ∼ G(n, p), each pair an edge independently with probability p → the published law LPCommunity.SBMRecovery.erProb n p (edge weights clamp01 p); reason: clamp01 is the identity on [0, 1], which contains every p of the statement
--   - generalization: one fixed arbitrary ordering 1, …, n and an arbitrary choice of each u_t → every vertex order σ (a permutation of Fin n) and every choice rule pick; reason: the source's run is one of these runs for any graph, so the statement specializes to it
--   - encoding: choose an arbitrary u_t ∈ N(t) ∩ B_{t−1} → u_t = pick t (N(t) ∩ B_{t−1}) if it is a candidate, else the least candidate; reason: every choice sequence is realized by some pick; the run is total
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), Theorem 2.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_HalfIndMatch_Lval
import Definitions.Def_HalfIndMatch_greedyOut

open LPCommunity.SBMRecovery

namespace HalfIndMatch

/-- Theorem 2.1, p.9: fix `κ ∈ (0, 1)` and `ε ∈ (0, 1/2)`. There is `C = C(ε, κ) > 0` such that,
for all sufficiently large `n` and all `C/n ≤ p ≤ 1 − κ`, the output `M_n` of Greedy satisfies
`P[|M_n| ≥ (1/2 − ε)L] ≥ 1 − exp(−n^ε)`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), Theorem 2.1, p.9 (PDF p.11).

**Formalization Note** The event is "for every vertex order `σ` and every choice rule `pick`, the
Greedy output has at least `(1/2 − ε)L` edges", which contains the event for any one order and
any (possibly graph-dependent) choice of the `u_t`. `G ∼ G(n, p)` is the published law `erProb`.
-/
theorem theorem_2_1 (κ ε : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ, C / n ≤ p → p ≤ 1 - κ →
      1 - Real.exp (-((n : ℝ) ^ ε)) ≤
        erProb n p (fun G => ∀ (σ : Equiv.Perm (Fin n)) (pick : ℕ → Finset (Fin n) → Fin n),
          (1 / 2 - ε) * Lval n p ≤ ((greedyOut G σ pick).card : ℝ)) := by sorry

end HalfIndMatch
