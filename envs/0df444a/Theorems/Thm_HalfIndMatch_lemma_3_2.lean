-- Prove2me | Theorems.Thm_HalfIndMatch_lemma_3_2
-- name    : HalfIndMatch.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:15:55.323348+00:00
-- url     : https://prove2.me/theorems/559b4e0d-90fe-4cbd-ab00-e0ce8d12aca5
-- title:
--   Lemma 3.2 — $\mathbb P[\text{at least }s\text{ edges accepted after }t\mid\tau_r=t]\le\binom ns(1-p)^{2rs+\binom s2}$
-- statement:
--   Let $A$ be a deterministic online algorithm, $G\sim G(n,p)$ with $0\le p\le1$, and let $r\ge1$ and $s\ge0$ be integers. For every $t\in[n]$,
--
--   $$\mathbb P\big[\tau_r=t\text{ and at least }s\text{ edges are accepted after time }t\big]\le\binom{n}{s}(1-p)^{2rs+\binom{s}{2}}\;\mathbb P[\tau_r=t],$$
--
--   which for $\mathbb P[\tau_r=t]>0$ is the lemma's bound
--
--   $$\mathbb P[\text{at least }s\text{ edges are accepted after time }t\mid\tau_r=t]\le\binom{n}{s}(1-p)^{2rs+\binom{s}{2}}.$$
--
--   The edges accepted after time $t$ are those of $A_n(G)\setminus A_t(G)$.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - encoding: G ∼ G(n, p), each pair an edge independently with probability p → the published law LPCommunity.SBMRecovery.erProb n p (edge weights clamp01 p); reason: clamp01 is the identity on [0, 1], which contains every p of the statement
--   - encoding: Definition 2.2: choices are functions of previous choices and revealed adjacencies → rules next/accept of (G, S, M) with locality fields; an inspected vertex chosen means termination, an illegal partner means no acceptance; reason: every algorithm of Definition 2.2 is such a structure and every such structure runs as one
--   - reading: stated after 'we may assume that A is deterministic' (p.15) → A : OnlineAlg n, a deterministic online algorithm; reason: this is the lemma's setting in the paper
--   - encoding: conditional probability given τ_r = t, for t with P[τ_r = t] > 0 → the product form P[τ_r = t ∧ …] ≤ bound · P[τ_r = t] for every t ∈ [n]; reason: equivalent when P[τ_r = t] > 0, and trivially true when it is 0
--   - generalization: r and s of (6), p in the regime C/n ≤ p ≤ 1 − κ → all naturals r ≥ 1 and s, all p ∈ [0, 1]; reason: the lemma's proof uses no property of these values; it specializes to them
--   - encoding: at least s edges are accepted after time t → s ≤ |A_n(G) \ A_t(G)|; reason: accepted edges are never removed, so the edges accepted after round t are exactly A_n(G) \ A_t(G)
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), Lemma 3.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_HalfIndMatch_OnlineAlg
import Definitions.Def_HalfIndMatch_tauR

open LPCommunity.SBMRecovery

namespace HalfIndMatch

/-- Lemma 3.2, p.15: for a deterministic online algorithm `A`, `r ≥ 1`, `s ≥ 0` and every round
`t ∈ [n]`,
`P[τ_r = t and at least s edges are accepted after time t] ≤ C(n, s) (1 − p)^{2rs + C(s,2)} P[τ_r = t]`,
the product form of
`P[at least s edges are accepted after time t | τ_r = t] ≤ C(n, s) (1 − p)^{2rs + C(s,2)}`
for `P[τ_r = t] > 0`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), Lemma 3.2, p.15 (PDF p.17).

**Formalization Note** The conditional statement is multiplied out (it then also holds when
`P[τ_r = t] = 0`). The edges accepted after time `t` are `A_n(G) \ A_t(G)` (accepted edges are
never removed). `r` and `s` are arbitrary naturals with `r ≥ 1`, not only the values of (6);
`p ∈ [0, 1]`. -/
theorem lemma_3_2 {n : ℕ} (A : OnlineAlg n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r s : ℕ)
    (hr : 1 ≤ r) (t : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ n) :
    erProb n p (fun G => tauR A G r = (t : ℕ∞) ∧ s ≤ (At A G n \ At A G t).card) ≤
      (Nat.choose n s : ℝ) * (1 - p) ^ (2 * r * s + Nat.choose s 2) *
        erProb n p (fun G => tauR A G r = (t : ℕ∞)) := by sorry

end HalfIndMatch
