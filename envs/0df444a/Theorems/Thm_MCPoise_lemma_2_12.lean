-- Prove2me | Theorems.Thm_MCPoise_lemma_2_12
-- name    : MCPoise.lemma_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:30:14.855376+00:00
-- url     : https://prove2.me/theorems/94eaa419-4295-4d6e-a5a8-2f861830c498
-- title:
--   Lemma 2.12 — $|S^*_j| \le \frac56 |S_j|$, and removed terminals have a path of length at most $4L'_d$ to a center
-- statement:
--   Fix a group with root $r$, terminals $S$ and $S' \subseteq S$ with $|S| \le 3|S'|$. For each $t \in S'$ let a selected path of length at most $4L'_d$ join $t$ to another vertex of $S \cup \{r\}$, with its edges in $H$. Let $F$ be the graph of the endpoints of these paths, take a spanning forest of $F$ and a proper two-colouring of it, let $R$ consist of the terminals of $S'$ in the colour class containing more terminals of $S'$, and put $S^* := S \setminus R$.
--
--   **Lemma 2.12.**
--   $$|S^*| \le \frac56 |S|.$$
--   Moreover every terminal in $R$ has a path in $H$ of length at most $4L'_d$ to a vertex of $S^* \cup \{r\}$.
--
--   **Formalization Note** The forest, the colouring and the tie are quantified universally, since the page leaves them open.
--
--   Differences from the source:
--   - generalization: H is the union of the selected paths over all groups → any graph containing the selected paths of this group; reason: the union over all groups is one such graph, and the proof uses only this
--   - encoding: a selected path between t and another vertex of S⁺_j; the color class containing more terminals, ties arbitrary → the path written from t; a colour b with at least as many terminals of S′ as the other; reason: a path reversed is the same path, and every tie-break is such a b
--   - generalization: S′_j and the paths P_{j,t} constructed in Stages 1 and 2, for S_j ⊆ V ∖ {r_j} → any S′ ⊆ S with |S| ≤ 3|S′| and any paths of G from each t ∈ S′ to another vertex of S ∪ {r} with at most 4L′_d edges, with r ∉ S not assumed; reason: Lemma 2.9 and Lemma 2.11 give exactly these properties, and the proof (p.20) uses nothing else
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.12, p.19; proof, p.20

import Mathlib
import Definitions.Def_MCPoise_IsPathIn

namespace MCPoise

open scoped Classical in
/-- **Lemma 2.12 (choosing centers).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.12, p.19: "For every j ∈ [µ], |S*_j| ≤ (5/6)|S_j|. Moreover, every terminal in R_j = S_j \ S*_j has a path in H of length at most 4L′_d to a vertex of S*_j ∪ {r_j}."
With p.19: "For each group j, construct an undirected graph F_j on S⁺_j by adding an edge between the endpoints of each selected path P_{j,t}, t ∈ S′_j. ... Take a spanning forest of F_j and
properly two-color its vertices. Let R_j consist of the terminals in S′_j belonging to the color class containing more terminals of S′_j, breaking ties arbitrarily. Set S*_j := S_j \ R_j."

Fix a group, with `S′ ⊆ S`, `|S| ≤ 3|S′|` and, for each `t ∈ S′`, a selected path `P t` from `t` to another vertex `e t` of `S⁺ = S ∪ {r}` of length at most `4L′_d`, whose edges lie in `H`. For every spanning
forest `F′` of the graph `F` of the endpoints, every proper two-colouring `c` of `F′` and every colour `b` with at least as many terminals of `S′` as the other: `R` and `S*` satisfy both claims.

**Formalization Note.** The forest, the colouring and the tie are universally quantified, as the page leaves them open. A selected path is written from its terminal `t`. `H` is any graph containing the selected
paths, such as the union over all groups. -/
theorem lemma_2_12 {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V) (r : V)
    (S S' : Finset V) (Lp : ℕ) (hS' : S' ⊆ S) (hcount : S.card ≤ 3 * S'.card)
    (P : V → List V) (e : V → V)
    (hP : ∀ t ∈ S', IsPathIn G t (e t) (P t) ∧ e t ∈ insert r S ∧ e t ≠ t ∧
      (pEdges (P t)).length ≤ 4 * Lp)
    (hH : ∀ t ∈ S', ∀ x ∈ pEdges (P t), x ∈ H.edgeSet)
    (F F' : SimpleGraph V) (hF : ∀ u v, F.Adj u v ↔ u ≠ v ∧ ∃ t ∈ S', s(u, v) = s(t, e t))
    (hle : F' ≤ F) (hac : F'.IsAcyclic) (hspan : ∀ u v, F.Reachable u v → F'.Reachable u v)
    (c : V → Bool) (hc : ∀ u v, F'.Adj u v → c u ≠ c v) (b : Bool)
    (hb : (S'.filter fun t => c t = !b).card ≤ (S'.filter fun t => c t = b).card) :
    6 * (S \ S'.filter fun t => c t = b).card ≤ 5 * S.card ∧
      ∀ t ∈ S'.filter fun t => c t = b,
        ∃ u, (u ∈ S \ S'.filter (fun t => c t = b) ∨ u = r) ∧
          ∃ w : H.Walk t u, w.length ≤ 4 * Lp := by sorry

end MCPoise
