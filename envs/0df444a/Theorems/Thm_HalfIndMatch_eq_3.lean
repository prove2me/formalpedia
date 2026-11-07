-- Prove2me | Theorems.Thm_HalfIndMatch_eq_3
-- name    : HalfIndMatch.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:13:32.110974+00:00
-- url     : https://prove2.me/theorems/5db45dc0-2403-4f7c-b1cf-0c07f8e5c791
-- title:
--   Eq. (3) — $\mathbb P[S\text{ spans a maximal induced matching}]=\mathbb P[\mathcal A]\,\mathbb P[\mathcal B\mid\mathcal A]$
-- statement:
--   Let $S\subseteq[n]$, let $\mathcal A$ be the event that $G[S]$ is a perfect matching, and let $\mathcal B$ be the event that $R_S$, the set of vertices outside $S$ with no neighbour in $S$, is independent.
--
--   1. For every graph $G$, the set $S$ spans a maximal induced matching of $G$ if and only if $G[S]$ is a perfect matching and $R_S$ is independent.
--   2. Consequently, for $G\sim G(n,p)$ with $0<p<1$,
--
--   $$\mathbb P[S\text{ spans a maximal induced matching}]=\mathbb P[\mathcal A]\,\mathbb P[\mathcal B\mid\mathcal A].$$
--
--   This is the first step of the first-moment bound on small maximal induced matchings in the proof of Proposition 3.1.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - encoding: G ∼ G(n, p), each pair an edge independently with probability p → the published law LPCommunity.SBMRecovery.erProb n p (edge weights clamp01 p); reason: clamp01 is the identity on [0, 1], which contains every p of the statement
--   - generalization: 1 ≤ k < (1/2 − ε)L, |S| = 2k, C/n ≤ p ≤ 1 − κ → any vertex set S and any 0 < p < 1; reason: the identity holds for every S and p ∈ (0, 1); it specializes to the source's S and p
--   - encoding: the conditional probability P[B | A] → the ratio P[A ∧ B] / P[A]; reason: definition of conditional probability
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, eq. (3), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_HalfIndMatch_IsInducedMatching
import Definitions.Def_HalfIndMatch_Rset

open LPCommunity.SBMRecovery

namespace HalfIndMatch

/-- Eq. (3), p.13: for a vertex set `S`,
(i) `S` spans a maximal induced matching of `G` if and only if `G[S]` is a perfect matching
(event `A`) and `R_S` is an independent set (event `B`); and
(ii) under `G(n, p)`, `P[S spans a maximal induced matching] = P[A] · P[B | A]`, where
`P[B | A] = P[A ∧ B] / P[A]`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, eq. (3), p.13 (PDF p.15).

**Formalization Note** The probability is the published Erdős–Rényi law `erProb n p`. The
conditional probability is the ratio `P[A ∧ B] / P[A]`. Clause (i) is deterministic and holds for
every graph and every `S` (the paper's `|S| = 2k` is not needed). -/
theorem eq_3 {n : ℕ} (S : Finset (Fin n)) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ G : SimpleGraph (Fin n), SpansMaximal G S ↔ (IsPerfectOn G S ∧ IsIndep G (Rset G S))) ∧
    erProb n p (fun G => SpansMaximal G S) =
      erProb n p (fun G => IsPerfectOn G S) *
        (erProb n p (fun G => IsPerfectOn G S ∧ IsIndep G (Rset G S)) /
          erProb n p (fun G => IsPerfectOn G S)) := by sorry

end HalfIndMatch
