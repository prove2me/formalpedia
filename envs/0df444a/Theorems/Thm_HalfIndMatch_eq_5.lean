-- Prove2me | Theorems.Thm_HalfIndMatch_eq_5
-- name    : HalfIndMatch.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:14:01.49371+00:00
-- url     : https://prove2.me/theorems/4afcdbdf-f2a1-431f-97ec-6aa37713f4e7
-- title:
--   Eq. (5) — $\mathbb P[\mathcal B\mid\mathcal A]=\mathbb E\big[(1-p)^{\binom{|R_S|}2}\big]$
-- statement:
--   Let $S\subseteq[n]$ with $|S|=2k$ and let $G\sim G(n,p)$ with $0<p<1$. With $\mathcal A$, $\mathcal B$ and $R_S$ as in eq. (3),
--
--   $$\mathbb P[\mathcal B\mid\mathcal A]=\mathbb E\Big[(1-p)^{\binom{|R_S|}{2}}\Big],$$
--
--   where the expectation is over $G\sim G(n,p)$, not conditioned on $\mathcal A$. The reason is that $\mathcal A$ depends only on the pairs inside $S$, $R_S$ only on the pairs between $S$ and its complement, and $\mathcal B$ given $R_S$ only on the pairs inside $R_S$.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - encoding: G ∼ G(n, p), each pair an edge independently with probability p → the published law LPCommunity.SBMRecovery.erProb n p (edge weights clamp01 p); reason: clamp01 is the identity on [0, 1], which contains every p of the statement
--   - generalization: 1 ≤ k < (1/2 − ε)L and C/n ≤ p ≤ 1 − κ → every k ≥ 0 and every 0 < p < 1; reason: the identity holds for every such k and p; it specializes to the source's range
--   - encoding: the conditional probability P[B | A] → the ratio P[A ∧ B] / P[A]; reason: definition of conditional probability
--   - encoding: E over G ∼ G(n, p) → Σ_G edgeWeight G p · (1 − p)^{C(|R_S|, 2)}; reason: the expectation of a function of G under the law erProb is this weighted sum
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, eq. (5), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_HalfIndMatch_Rset

open LPCommunity.SBMRecovery

namespace HalfIndMatch

/-- Eq. (5), p.13: if `|S| = 2k` and `0 < p < 1` then, under `G(n, p)`,
`P[B | A] = E[(1 − p)^{C(|R_S|, 2)}]`, where `A` is the event that `G[S]` is a perfect matching,
`B` the event that `R_S` is independent, and the expectation is over `G ∼ G(n, p)` without
conditioning.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, eq. (5), p.13 (PDF p.15).

**Formalization Note** `P[B | A]` is `P[A ∧ B] / P[A]`; `P[A] > 0` because `|S|` is even and
`0 < p < 1`. The expectation is the sum over all graphs weighted by the `G(n, p)` law. -/
theorem eq_5 {n : ℕ} (k : ℕ) (S : Finset (Fin n)) (hS : S.card = 2 * k) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) :
    erProb n p (fun G => IsPerfectOn G S ∧ IsIndep G (Rset G S)) /
        erProb n p (fun G => IsPerfectOn G S) =
      ∑ G : SimpleGraph (Fin n),
        edgeWeight G (fun _ _ => p) * (1 - p) ^ Nat.choose (Rset G S).card 2 := by sorry

end HalfIndMatch
