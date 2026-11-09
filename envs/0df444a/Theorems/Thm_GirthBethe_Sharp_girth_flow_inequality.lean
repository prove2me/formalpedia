-- Prove2me | Theorems.Thm_GirthBethe_Sharp_girth_flow_inequality
-- name    : GirthBethe.Sharp.girth_flow_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:19:25.730476+00:00
-- url     : https://prove2.me/theorems/d22d4936-50ea-41db-a982-af9080108f22
-- title:
--   Proposition 4.6 — the girth inequality for $J^\pm$
-- statement:
--   Let $g\ge4$ be even, let $G=(L\sqcup R,E)$ be a finite simple bipartite graph of girth at least $g$, and fix $\star\in L$. Let $J_e^+,J_e^-\ge0$ be edge weights, and put $J_v^\pm=\sum_{e\ni v}J_e^\pm$. Suppose that at every vertex $v$,
--   $$J_v^-\le J_v^+,\qquad J_e^-\le\sum_{\substack{f\ni v\\f\ne e}}J_f^+\quad(e\ni v).$$
--   Then
--   $$gJ_\star^+\le\sum_{v\in L\sqcup R}J_v^-+
--   \frac{g-2}{2}\sum_{v\in L\sqcup R}(J_v^+-J_v^-)+2(J_\star^+-J_\star^-).$$
--   This is the girth inequality for the auxiliary information flow, stated for all nonnegative weights allowed by the p. 12 preamble. The weights of Definition 4.1 are included by Lemma 4.2.
--
--   Differences from the source:
--   - encoding: a finite simple bipartite graph G = (L ⊔ R, E) → finite types L and R and an edge finset E ⊆ L × R; vertexWeight J v = ∑_{e ∋ v} J_e; reason: each edge has exactly one endpoint in each class; no extra graph condition is introduced
--   - encoding: girth at least g with forests having infinite girth → (g : ℕ∞) ≤ (toGraph E).egirth; reason: the same shortest-cycle convention, including forests
--   - generalization: J_e^± associated with the distinguished left vertex ⋆ and its matching law, with arbitrary weights allowed by the p. 12 preamble → arbitrary nonnegative J^± on any finite bipartite graph satisfying both Lemma 4.2 inequalities at every vertex; reason: the component bounds and the flow reassembly use exactly these conditions; law-derived weights satisfy them by Lemma 4.2, recovering the complete source proposition
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 14, Proposition 4.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_FlowNetwork

open Finset

namespace GirthBethe.Sharp

open scoped Classical in
/-- Proposition 4.6 for the arbitrary weights permitted on p. 12, with both inequalities
of Lemma 4.2; the law-derived weights are a special case. -/
theorem girth_flow_inequality {L R : Type*} [Fintype L] [Fintype R]
    (E : Finset (L × R))
    (g : ℕ) (hg : Even g) (hg4 : 4 ≤ g) (hgirth : (g : ℕ∞) ≤ (toGraph E).egirth)
    (Jp Jm : Edge E → ℝ) (hp : ∀ e, 0 ≤ Jp e) (hm : ∀ e, 0 ≤ Jm e)
    (htotal : ∀ v, vertexWeight Jm v ≤ vertexWeight Jp v)
    (hoff : ∀ v, ∀ e : Edge E, Inc v e.1 →
      Jm e ≤ ∑ f with Inc v f.1 ∧ f ≠ e, Jp f) (star : L) :
    (g : ℝ) * vertexWeight Jp (Sum.inl star) ≤
      (∑ v : L ⊕ R, vertexWeight Jm v) +
        (((g : ℝ) - 2) / 2) * (∑ v : L ⊕ R, (vertexWeight Jp v - vertexWeight Jm v)) +
        2 * (vertexWeight Jp (Sum.inl star) - vertexWeight Jm (Sum.inl star)) := by sorry

end GirthBethe.Sharp
