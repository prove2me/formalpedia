-- Prove2me | Theorems.Thm_HalfIndMatch_spans_maximal_le
-- name    : HalfIndMatch.spans_maximal_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:14:12.024495+00:00
-- url     : https://prove2.me/theorems/a4f86a92-4be8-4e66-b69b-bfb49f2e4192
-- title:
--   §3.1, display after (5), p.13 — $\mathbb P[S\text{ spans a maximal induced matching}]\le\frac{(2k)!}{2^{k-1}k!}(1-p)^{\binom{2k}2-k}p^ke^{-(np)^{2\varepsilon}/(20p)}$
-- statement:
--   Fix $\kappa\in(0,1)$ and $\varepsilon\in(0,1/2)$, and let $L$ be as in (1). There are $C>1$ and $N$ such that for all $n\ge N$, all $C/n\le p\le1-\kappa$, all integers $1\le k<(1/2-\varepsilon)L$ and all $S\subseteq[n]$ with $|S|=2k$, for $G\sim G(n,p)$,
--
--   $$\mathbb P[S\text{ spans a maximal induced matching}]\le\frac{(2k)!}{2^{k-1}\,k!}\,(1-p)^{\binom{2k}{2}-k}\,p^k\exp\Big(-\frac{(np)^{2\varepsilon}}{20p}\Big).$$
--
--   It combines (3), (4), (5) with a Chernoff bound on $|R_S|\sim\mathrm{Binomial}(n-2k,(1-p)^{2k})$.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - encoding: G ∼ G(n, p), each pair an edge independently with probability p → the published law LPCommunity.SBMRecovery.erProb n p (edge weights clamp01 p); reason: clamp01 is the identity on [0, 1], which contains every p of the statement
--   - reading: a display inside the proof of Proposition 3.1, valid 'for C sufficiently large' in that proof's setting → ∃ C > 1, ∃ N, ∀ n ≥ N, ∀ p ∈ [C/n, 1 − κ], ∀ k with 1 ≤ k < (1/2 − ε)L; reason: these are the quantifiers of Proposition 3.1, within whose proof the display is stated
--   - encoding: exponents k − 1 and C(2k,2) − k → natural-number subtraction; reason: exact for k ≥ 1
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, display after (5), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_HalfIndMatch_Lval
import Definitions.Def_HalfIndMatch_Rset

open LPCommunity.SBMRecovery

namespace HalfIndMatch

/-- §3.1, the display at the end of p.13 ("Combining (3), (4), (5), and the above"): for fixed
`κ ∈ (0, 1)` and `ε ∈ (0, 1/2)` there are `C > 1` and `N` such that for all `n ≥ N`,
`C/n ≤ p ≤ 1 − κ`, `1 ≤ k < (1/2 − ε)L` and `|S| = 2k`,
`P[S spans a maximal induced matching] ≤ (2k)!/(2^{k−1} k!) (1 − p)^{C(2k,2)−k} p^k exp(−(np)^{2ε}/(20p))`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, display after (5), p.13 (PDF p.15).

**Formalization Note** The quantifiers are those of Proposition 3.1, inside whose proof the display
sits. `k − 1` and `C(2k, 2) − k` are natural-number subtractions, exact for `k ≥ 1`.
`(np)^{2ε}` is `Real.rpow`. -/
theorem spans_maximal_le (κ ε : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 1 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ, C / n ≤ p → p ≤ 1 - κ →
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) < (1 / 2 - ε) * Lval n p →
        ∀ S : Finset (Fin n), S.card = 2 * k →
          erProb n p (fun G => SpansMaximal G S) ≤
            (Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ (k - 1) * (Nat.factorial k : ℝ)) *
              (1 - p) ^ (Nat.choose (2 * k) 2 - k) * p ^ k *
                Real.exp (-(((n : ℝ) * p) ^ (2 * ε) / (20 * p))) := by sorry

end HalfIndMatch
