-- Prove2me | Theorems.Thm_NetworkSumSecure_Solvability_theorem_1
-- name    : NetworkSumSecure.Solvability.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:03:27.672127+00:00
-- url     : https://prove2.me/theorems/e98ad300-c81d-41d3-9a3a-d53ed7690f25
-- title:
--   Theorem 1 — operational solvability iff mincut is at least r+1
-- statement:
--   Let $N$ be any finite directed acyclic multigraph with distinct user vertices and one distinct server. Users have no incoming edges, the server has no outgoing edges, and every nonserver vertex has a directed path to the server. Let $r\ge0$, let $c(N)$ be the minimum number of edges meeting every user-to-server path, and let $\mathcal W_r=\{W\subseteq E:|W|\le r\}$.
--
--   For every finite field $F$, solvability implies the cut bound, independently of the field size:
--
--   $$\operatorname{Solvable}_F(N,r)\ \Longrightarrow\ c(N)\ge r+1.$$
--
--   There is a threshold $Q_0(N,r)=|U|+|\mathcal W_r|+1$, chosen before the field, such that for every finite field $F$ of any characteristic with $|F|\ge Q_0(N,r)$,
--
--   $$\begin{aligned}
--   \operatorname{Solvable}_F(N,r)&\ \Longleftrightarrow\ c(N)\ge r+1,\\
--   \operatorname{Solvable}_F(N,r)&\ \Longleftrightarrow\ \text{there exist at least }r+1\text{ edge-disjoint user-to-server paths}.
--   \end{aligned}$$
--
--   Solvability existentially supplies nonnegative private-key counts, causal local scalar linear encoders and a correct linear server decoder. It requires equation (7) for all observations on every wiretap set of size at most $r$, counting keys once with an existential deterministic input witness. The key factors are independent and private to their users. Parallel edges retain distinct identities, paths may share vertices, and no shared keys or relay randomness is supplied.
--
--   This is the complete sharp graph characterization, including both iff directions and the equivalent path clause. It allows $r=0$, zero key counts and arbitrary security levels relative to the number of edges.
--
--   **Formalization Note** The explicit threshold witnesses the source's sufficiently-large-field convention using (34) and (53); it is not asserted optimal. An empty user set is also allowed: its input sum is always zero, so the security probabilities at the empty wiretap set differ for sum values zero and one, while its mincut is zero and no positive number of user paths exists.
--
--   Differences from the source:
--   - encoding: the field is sufficiently large as stipulated in §2.1 footnote 1 → there exists Q₀=s+|W_r|+1 before universally quantifying every finite field F with |F|≥Q₀; reason: this uniform witness follows from (34) and (53) and leaves all finite field characteristics available
--   - generalization: the theorem is stated under the sufficiently-large-field convention → the converse solvability⇒mincut≥r+1 is additionally asserted for every finite field; reason: the direct cut argument (10)–(14) uses no lower bound on the field size
--   - generalization: a nonempty collection of participants is implicit → arbitrary finite user index sets, including the empty set; reason: at the empty set the key-event security condition fails and both graph criteria are false, so the equivalences remain true
--   - encoding: finite graph paths, linear local schemes and uniform key probabilities → labelled-edge lists, topological local execution and exact rational counting of existential-input key events; reason: these representations preserve every parallel edge, every local information restriction and every key-event probability
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), p. 9 (PDF p. 11); converse pp. 9–10 (PDF pp. 11–12); model pp. 5–8 (PDF pp. 7–10); field bounds p. 16 (PDF p. 18), p. 23 (PDF p. 25), Theorem 1, equation (9), §3.1 equations (10)–(14), §2.1 footnote 1, equations (34), (53)

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_encoding

namespace NetworkSumSecure.Solvability

/-- Theorem 1, printed p.9 (PDF 11), including the field-independent converse.
The explicit Q₀ witnesses the standing field-size convention via (34) and (53).
Empty user types are allowed: the security definition then fails even at W=empty. -/
theorem theorem_1 {V E U : Type} [Fintype V] [Fintype E] [Fintype U]
    (N : Network V E U) (r : ℕ) :
    (∀ (F : Type) [Field F] [Fintype F],
      Solvable (F := F) N r → r + 1 ≤ mincut N) ∧
    ∃ Q₀ : ℕ, Q₀ = fieldThreshold (E := E) (U := U) r ∧
      ∀ (F : Type) [Field F] [Fintype F], Q₀ ≤ Fintype.card F →
        ((Solvable (F := F) N r ↔ r + 1 ≤ mincut N) ∧
          (Solvable (F := F) N r ↔ HasPaths N (r + 1))) := by sorry

end NetworkSumSecure.Solvability
