-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_3_3
-- name    : LCPlanarSteiner.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:46.870747+00:00
-- url     : https://prove2.me/theorems/8967acfb-b513-404b-bb61-51430bc8a4fc
-- title:
--   Lemma 3.3 — forward profile: $1 + \lceil (M+L_0)/\delta\rceil$ extensions give arrivals $\le A(v) + \delta$ on $P$
-- statement:
--   Let $G$ be a graph with nonnegative costs and lengths, $r$ a root, $F$ the purchased arcs, and let the arrivals $A$ with extensions $Q_u$ arrive by $A$ (as returned by Lemma 3.2). Let $P$ be a simple directed path with $\ell(P) \le L_0$, and $M, \delta > 0$.
--
--   **Lemma 3.3 (Forward profile).** There is a set $U$ of vertices of $P$ with
--   $$
--   |U| \le 1 + \Bigl\lceil \frac{M + L_0}{\delta} \Bigr\rceil
--   $$
--   such that, after buying $P$ and the extensions $Q_u$ for $u \in U$, every vertex $v$ of $P$ with $A(v) \le M$ has a paid arrival
--   $$
--   \mathrm{dist}_{F \cup P \cup \bigcup_{u \in U} Q_u}(r, v) \le A(v) + \delta .
--   $$
--
--   Profiles let the recursion pay for few extensions per separator path while losing only an additive $\delta$ per depth.
--
--   Differences from the source:
--   - generalization: extensions from Lemma 3.2 → any arrivals and extensions with the arrives-by property; reason: the proof uses only that property, which Lemma 3.2's output has
--   - encoding: a paid arrival → the distance from r in the purchased union F ∪ P ∪ ⋃ Q_u; reason: the paper's meaning (p.6, "its purchased extension followed by P[u, v] gives that arrival")
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.3, p.6

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_DistLE
import Definitions.Def_LCPlanarSteiner_ArrivesBy

namespace LCPlanarSteiner

/-- **Lemma 3.3 (Forward profile).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.3, p.6: "Let a directed path P have length at most L₀. For M, δ > 0, at most
1 + ⌈(M + L₀)/δ⌉ extensions from lemma 3.2, together with P, give every vertex with A(v) ≤ M a paid
arrival at most A(v) + δ."

Let `G` be a well-formed graph with root `r`, owned arcs `E_R`, boundary `B`, purchased arcs `F`,
and arrivals `A` with extensions `Q` that arrive by `A` (`ArrivesBy`). Let `P` be a simple directed
path from `u₀` to `u₁` with `ℓ(P) ≤ L₀`, and `M, δ > 0`. Then there is a set `U` of vertices of
`P` with `|U| ≤ 1 + ⌈(M + L₀)/δ⌉` such that, after buying `P` and the extensions `Q_u` (`u ∈ U`),
every vertex `v` of `P` with `A(v) ≤ M` has `dist(r, v) ≤ A(v) + δ` in `F ∪ P ∪ ⋃_{u∈U} Q_u`.

**Formalization Note.** "Extensions from lemma 3.2" are any arrivals and extensions with the
arrives-by property; the proof uses nothing else. A "paid arrival" is the distance from `r` in the
purchased union. The arcs of `P` need not be owned. -/
theorem lemma_3_3 (G : Net) (hG : G.WF) (ER B F : Finset ℕ) (r : ℕ) (A : ℕ → WithTop ℚ)
    (Q : ℕ → List ℕ) (hA : ArrivesBy G ER B F r A Q) (u₀ u₁ : ℕ) (P : List ℕ)
    (hP : IsSPath G u₀ u₁ P) (L₀ M δ : ℚ) (hL : plen G P ≤ L₀) (hM : 0 < M) (hδ : 0 < δ) :
    ∃ U : Finset ℕ, (∀ u ∈ U, u ∈ verts G u₀ P) ∧
      (U.card : ℚ) ≤ 1 + ⌈(M + L₀) / δ⌉₊ ∧
      ∀ v ∈ verts G u₀ P, ∀ a : ℚ, A v = a → a ≤ M →
        DistLE G (F ∪ P.toFinset ∪ U.biUnion fun u => (Q u).toFinset) r v (a + δ) := by sorry

end LCPlanarSteiner
