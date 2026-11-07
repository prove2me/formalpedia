-- Prove2me | Theorems.Thm_HalfIndMatch_eq_8
-- name    : HalfIndMatch.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:16:00.331927+00:00
-- url     : https://prove2.me/theorems/1a86637d-4a21-4e77-b938-f8ef405cb901
-- title:
--   Eq. (8) — $\mathbb P[|A_n(G)|\ge m^*]\le\binom ns(1-p)^{2rs+\binom s2}$
-- statement:
--   Let $A$ be a deterministic online algorithm, $G\sim G(n,p)$ with $0\le p\le1$, and let $1\le r\le m$ be integers and $s=m-r$. Then
--
--   $$\mathbb P[|A_n(G)|\ge m]=\mathbb P[\tau_r<\infty,\ |A_n(G)|\ge m]\le\binom{n}{s}(1-p)^{2rs+\binom{s}{2}}.$$
--
--   With $m=m^*$ and $r$ of (6) this is the bound (8) from which Theorem 2.3 follows by the estimate (10).
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - encoding: G ∼ G(n, p), each pair an edge independently with probability p → the published law LPCommunity.SBMRecovery.erProb n p (edge weights clamp01 p); reason: clamp01 is the identity on [0, 1], which contains every p of the statement
--   - encoding: Definition 2.2: choices are functions of previous choices and revealed adjacencies → rules next/accept of (G, S, M) with locality fields; an inspected vertex chosen means termination, an illegal partner means no acceptance; reason: every algorithm of Definition 2.2 is such a structure and every such structure runs as one
--   - reading: stated after 'we may assume that A is deterministic' (p.15) → A : OnlineAlg n, a deterministic online algorithm; reason: this is the lemma's setting in the paper
--   - generalization: m* and r of (6), treated as integers, p in the regime → all naturals 1 ≤ r ≤ m with s = m − r, all p ∈ [0, 1]; reason: the derivation uses only r ≤ m; it specializes to (6)
--   - reading: the printed chain with the intermediate sums over t → the first equality and the final bound; reason: the intermediate sums are the steps (total probability, Lemma 3.2) between the stated ends
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), eq. (8), §3.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_HalfIndMatch_OnlineAlg
import Definitions.Def_HalfIndMatch_tauR

open LPCommunity.SBMRecovery

namespace HalfIndMatch

/-- Eq. (8), p.15: for a deterministic online algorithm `A`, `p ∈ [0, 1]` and naturals
`1 ≤ r ≤ m` with `s = m − r`,
`P[|A_n(G)| ≥ m] = P[τ_r < ∞, |A_n(G)| ≥ m] ≤ C(n, s)(1 − p)^{2rs + C(s,2)}`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), eq. (8), §3.2, p.15 (PDF p.17).

**Formalization Note** Stated for all naturals `1 ≤ r ≤ m` (the paper's `m^*`, `r` of (6) treated as
integers). `m − r` is natural-number subtraction, exact since `r ≤ m`. The middle sums over `t` of
the printed chain are a proof step. -/
theorem eq_8 {n : ℕ} (A : OnlineAlg n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r m : ℕ)
    (hr : 1 ≤ r) (hrm : r ≤ m) :
    erProb n p (fun G => m ≤ (output A G).card) =
        erProb n p (fun G => tauR A G r ≠ ⊤ ∧ m ≤ (output A G).card) ∧
      erProb n p (fun G => m ≤ (output A G).card) ≤
        (Nat.choose n (m - r) : ℝ) * (1 - p) ^ (2 * r * (m - r) + Nat.choose (m - r) 2) := by sorry

end HalfIndMatch
