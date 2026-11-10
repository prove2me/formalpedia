-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_7_4
-- name    : LoadBalMatch.Main.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:34:03.487261+00:00
-- url     : https://prove2.me/theorems/4ecab15e-a358-4f3f-9be5-26f39bea2ff4
-- title:
--   Lemma 7.4 — an external matching between $A\cup C$ and $D$ lowers $\eta$ by $w(M)/8$
-- statement:
--   Let $H$ be a graph on the finite set $V$, $x\in P(H)$ a balanced fractional matching on $H$ with level vector $\ell$ (in $H$), and $(D,A,C)$ the Gallai–Edmonds decomposition of $H$. Let $M$ be a matching (pairwise disjoint vertex pairs) whose edges are not edges of $H$ and each join a vertex of $A\cup C$ to a vertex of $D$. Give $e=(u,v)\in M$, $u\in A\cup C$, $v\in D$, the weight $w(e)=(\ell_u-x_v)^2$ if $\ell_u>x_v$ and $w(e)=0$ otherwise, and let $w(M)=\sum_{e\in M}w(e)$. Then there is a (not necessarily balanced) fractional matching $y\in P(H\cup M)$ with
--   $$\sum_{v\in V}(1-x_v)^2-\sum_{v\in V}(1-y_v)^2\ \ge\ \frac{w(M)}{8}.$$
--
--   This is the progress guarantee of the external-matching step of Algorithms 3 and 4.
--
--   Differences from the source:
--   - encoding: w(e) = (ℓ_u − x_v)² for e = (u, v) ∈ M with u ∈ A ∪ C, v ∈ D, ℓ_u > x_v, else 0 → extWeight H x e, eq. (36) on unordered pairs (the sum over both orientations, at most one nonzero); reason: same value on every edge of M
--   - encoding: M a matching between A ∪ C and D using edges outside H → IsMatchingIn ⊤ M (pairwise disjoint non-loop pairs), no element an edge of H, each element s(u, v) with u ∈ A ∪ C, v ∈ D; reason: same objects
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 34, Lemma 7.4

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_GallaiEdmonds
import Definitions.Def_LoadBalMatch_Main_Violation

namespace LoadBalMatch.Main

theorem lemma_7_4 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (x : Sym2 V → ℝ) (hx : IsBalanced H x) (M : Finset (Sym2 V))
    (hM : IsMatchingIn (⊤ : SimpleGraph V) M) (hMout : ∀ e ∈ M, e ∉ H.edgeSet)
    (hMbetween : ∀ e ∈ M, ∃ u v, e = s(u, v) ∧ u ∈ gA H ∪ gC H ∧ v ∈ gD H) :
    ∃ y : Sym2 V → ℝ, IsFracMatching (addEdges H ↑M) y ∧
      (∑ e ∈ M, extWeight H x e) / 8 ≤ eta x - eta y := by sorry

end LoadBalMatch.Main
