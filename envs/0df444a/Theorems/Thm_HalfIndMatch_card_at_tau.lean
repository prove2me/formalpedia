-- Prove2me | Theorems.Thm_HalfIndMatch_card_at_tau
-- name    : HalfIndMatch.card_at_tau
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:15:59.353768+00:00
-- url     : https://prove2.me/theorems/83934799-38ee-45e1-aac0-b4a15e606146
-- title:
--   §3.2, claim after (7), p.15 — one edge per round, so $|A_{\tau_r}(G)|=r$ whenever $\tau_r<\infty$
-- statement:
--   Let $A$ be a deterministic online algorithm and $G$ a graph on $[n]$. Accepted edges are never removed and at most one edge is accepted per round:
--
--   $$A_t(G)\subseteq A_{t+1}(G),\qquad |A_{t+1}(G)|\le|A_t(G)|+1\qquad(t\ge0).$$
--
--   In particular, for every $r\ge1$, $|A_{\tau_r}(G)|=r$ whenever $\tau_r<\infty$.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - encoding: Definition 2.2: choices are functions of previous choices and revealed adjacencies → rules next/accept of (G, S, M) with locality fields; an inspected vertex chosen means termination, an illegal partner means no acceptance; reason: every algorithm of Definition 2.2 is such a structure and every such structure runs as one
--   - reading: stated after 'we may assume that A is deterministic' (p.15) → A : OnlineAlg n, a deterministic online algorithm; reason: this is the lemma's setting in the paper
--   - generalization: r of (6) (and τ_r for that r) → every natural r ≥ 1; reason: the claim holds for every r ≥ 1; it specializes to r of (6)
--   - generalization: rounds t ∈ [n] → every t : ℕ (the clauses on A_t ⊆ A_{t+1} and |A_{t+1}| ≤ |A_t| + 1); reason: rounds after n change nothing (the algorithm has terminated, A_t = M_out), so the extra instances are trivial and the statement specializes to t ∈ [n]
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), §3.2, the sentence after (7), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_HalfIndMatch_OnlineAlg
import Definitions.Def_HalfIndMatch_tauR

namespace HalfIndMatch

/-- §3.2, the claim after (7), p.15: for every online algorithm `A` and graph `G`, accepted edges
are never removed and at most one edge is accepted per round,
`A_t(G) ⊆ A_{t+1}(G)` and `|A_{t+1}(G)| ≤ |A_t(G)| + 1`; in particular `|A_{τ_r}(G)| = r`
whenever `τ_r < ∞` (here for `r ≥ 1`).

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), §3.2, the sentence after (7), p.15 (PDF p.17).

**Formalization Note** Deterministic algorithms (the paper has reduced to them at this point). -/
theorem card_at_tau {n : ℕ} (A : OnlineAlg n) (G : SimpleGraph (Fin n)) :
    (∀ t : ℕ, At A G t ⊆ At A G (t + 1) ∧ (At A G (t + 1)).card ≤ (At A G t).card + 1) ∧
    ∀ r : ℕ, 1 ≤ r → ∀ t : ℕ, tauR A G r = (t : ℕ∞) → (At A G t).card = r := by sorry

end HalfIndMatch
