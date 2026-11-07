-- Prove2me | Theorems.Thm_HalfIndMatch_maximal_of_size_k_le
-- name    : HalfIndMatch.maximal_of_size_k_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:11:40.441207+00:00
-- url     : https://prove2.me/theorems/6d878f41-b51b-44f5-aadb-10956e8e9609
-- title:
--   §3.1, display on p.14 — $\mathbb P[G\text{ contains a maximal induced matching of size }k]\le e^{-(np)^{2\varepsilon}/(30p)}$
-- statement:
--   Fix $\kappa\in(0,1)$ and $\varepsilon\in(0,1/2)$, and let $L$ be as in (1). There are $C>1$ and $N$ such that for all $n\ge N$, all $C/n\le p\le1-\kappa$ and all integers $1\le k<(1/2-\varepsilon)L$, for $G\sim G(n,p)$,
--
--   $$\mathbb P[G\text{ contains a maximal induced matching of size }k]\le\exp\Big(-\frac{(np)^{2\varepsilon}}{30p}\Big).$$
--
--   Summed over the possible sizes $k$, this gives Proposition 3.1.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - encoding: G ∼ G(n, p), each pair an edge independently with probability p → the published law LPCommunity.SBMRecovery.erProb n p (edge weights clamp01 p); reason: clamp01 is the identity on [0, 1], which contains every p of the statement
--   - reading: a display inside the proof of Proposition 3.1, valid 'for C sufficiently large' in that proof's setting → ∃ C > 1, ∃ N, ∀ n ≥ N, ∀ p ∈ [C/n, 1 − κ], ∀ k with 1 ≤ k < (1/2 − ε)L; reason: these are the quantifiers of Proposition 3.1, within whose proof the display is stated
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, display on p.14 (PDF p.16)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_HalfIndMatch_IsInducedMatching
import Definitions.Def_HalfIndMatch_Lval

open LPCommunity.SBMRecovery

namespace HalfIndMatch

/-- §3.1, display on p.14: for fixed `κ ∈ (0, 1)` and `ε ∈ (0, 1/2)` there are `C > 1` and `N`
such that for all `n ≥ N`, `C/n ≤ p ≤ 1 − κ` and `1 ≤ k < (1/2 − ε)L`,
`P[G contains a maximal induced matching of size k] ≤ exp(−(np)^{2ε}/(30p))`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, display on p.14 (PDF p.16).

**Formalization Note** The quantifiers are those of Proposition 3.1, inside whose proof the display
sits. `(np)^{2ε}` is `Real.rpow`. -/
theorem maximal_of_size_k_le (κ ε : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hε0 : 0 < ε)
    (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 1 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ, C / n ≤ p → p ≤ 1 - κ →
      ∀ k : ℕ, 1 ≤ k → (k : ℝ) < (1 / 2 - ε) * Lval n p →
        erProb n p (fun G => ∃ M : Finset (Sym2 (Fin n)),
            IsMaximalInducedMatching G M ∧ M.card = k) ≤
          Real.exp (-(((n : ℝ) * p) ^ (2 * ε) / (30 * p))) := by sorry

end HalfIndMatch
