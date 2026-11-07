-- Prove2me | Theorems.Thm_HalfIndMatch_eq_4
-- name    : HalfIndMatch.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:13:33.085116+00:00
-- url     : https://prove2.me/theorems/e27f6eff-84cb-4203-9015-8da4baa0bb38
-- title:
--   Eq. (4) — $\mathbb P[\mathcal A]=\frac{(2k)!}{2^kk!}(1-p)^{\binom{2k}2-k}p^k$
-- statement:
--   Let $S\subseteq[n]$ with $|S|=2k$ and let $G\sim G(n,p)$ with $0\le p\le1$. The probability that $G[S]$ is a perfect matching is
--
--   $$\mathbb P[\mathcal A]=\frac{(2k)!}{2^k\,k!}\,(1-p)^{\binom{2k}{2}-k}\,p^k,$$
--
--   since $S$ admits $(2k)!/(2^kk!)$ perfect matchings, each of which is $G[S]$ when its $k$ pairs are edges and the other $\binom{2k}2-k$ pairs inside $S$ are not.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - encoding: G ∼ G(n, p), each pair an edge independently with probability p → the published law LPCommunity.SBMRecovery.erProb n p (edge weights clamp01 p); reason: clamp01 is the identity on [0, 1], which contains every p of the statement
--   - generalization: 1 ≤ k < (1/2 − ε)L and C/n ≤ p ≤ 1 − κ → every k ≥ 0 and every p ∈ [0, 1]; reason: the count holds for every k and p; it specializes to the source's range
--   - encoding: exponent C(2k,2) − k → natural-number subtraction Nat.choose (2k) 2 − k; reason: exact, since C(2k, 2) = k(2k − 1) ≥ k
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, eq. (4), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_HalfIndMatch_Rset

open LPCommunity.SBMRecovery

namespace HalfIndMatch

/-- Eq. (4), p.13: if `|S| = 2k` then, under `G(n, p)`,
`P[G[S] is a perfect matching] = (2k)!/(2^k k!) · (1 − p)^{C(2k,2) − k} · p^k`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, eq. (4), p.13 (PDF p.15).

**Formalization Note** `Nat.choose (2 * k) 2 - k` is natural-number subtraction; it is exact because
`C(2k, 2) = k(2k − 1) ≥ k`. Stated for every `k ≥ 0` and `p ∈ [0, 1]`. -/
theorem eq_4 {n : ℕ} (k : ℕ) (S : Finset (Fin n)) (hS : S.card = 2 * k) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    erProb n p (fun G => IsPerfectOn G S) =
      (Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k * (Nat.factorial k : ℝ)) *
        (1 - p) ^ (Nat.choose (2 * k) 2 - k) * p ^ k := by sorry

end HalfIndMatch
