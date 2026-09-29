-- Prove2me | Theorems.Thm_Hirsch_larman_layer_recursion
-- name    : Hirsch.larman_layer_recursion
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:49:02.016716+00:00
-- url     : https://prove2.me/theorems/7c2fc172-5ec0-484c-a768-daddb50be23c
-- title:
--   Larman's layer recursion: summing the layer steps along a facet decomposition
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i<n\}$ be a bounded H-polytope with all normals nonzero, in which every vertex has at least one tight inequality. Let $\beta:\mathbb{N}\to\mathbb{N}$ and $B_d\in\mathbb{N}$. Assume:
--
--   1. **(layer step)** for every base vertex $u$, row $r$, set of rows $T\ni r$, and vertices $y,z$ on the facet $F_r$ with tight rows in $T$ such that every vertex of $F_r$ carrying a row outside $T$ is strictly closer to $u$ than $y$, one has $\mathrm{gdist}(u,z)\le\mathrm{gdist}(u,y)+\beta(|T|)$ (this is `Hirsch.larman_layer_step`);
--   2. **(arithmetic)** for every $k$ and every family $m_1,\dots,m_k\ge1$ with $\sum_i m_i\le 2n$,
--   $$\sum_{i=1}^{k}\beta(m_i)+k\ \le\ B_d+1 .$$
--
--   Then $\operatorname{DiamLE}(P,B_d)$: the combinatorial diameter of $P$ is at most $B_d$.
--
--   This is Larman's argument as presented by Kim--Santos. From a base vertex $u$, stratify the vertices by distance into layers $V_1,\dots,V_k$ with $V_i=\{v:\delta_{i-1}<\mathrm{gdist}(u,v)\le\delta_i\}$, $\delta_0=-1$, where $\delta_i$ is the largest distance of a vertex sharing a facet $F_i$ with some vertex at distance $\delta_{i-1}+1$. Let $T_i$ be the rows tight at some vertex of $V_i$ and $m_i=|T_i|$. Because a facet active in two layers is active in all layers between (`Hirsch.tight_row_interval`) and the choice of $F_{i+1}$ is maximal, no row is active in three layers, so $\sum_i m_i\le2n$. The layer step applied to $F_i$, $T_i$, a vertex $y_i\in F_i$ at distance $\delta_{i-1}+1$ and a vertex $z_i\in F_i$ at distance $\delta_i$ gives $\delta_i-\delta_{i-1}-1\le\beta(m_i)$, and summing over $i$ yields $\mathrm{ecc}(u)=\delta_k\le\sum_i\beta(m_i)+k-1\le B_d$.
--
--   **Formalization Note** The hypothesis that every vertex has a tight row holds automatically when $d\ge1$ (the tight normals span, `Hirsch.vertex_tight_rows_span`), and is stated explicitly to keep the recursion dimension-free. The layer-step hypothesis is quantified over all base vertices $u$ and all finsets $T$ of rows.
-- source:
--   D. G. Larman, Paths on polytopes, Proc. London Math. Soc. s3-20 (1970) 161-178, https://doi.org/10.1112/plms/s3-20.2.249; exposition followed: E. D. Kim, F. Santos, Companion to 'An update on the Hirsch conjecture', arXiv:0912.4235, Section 2.2, proof of Theorem 2.5 (layer decomposition, 'no facet is active in more than two V_i's', sum n_i <= 2n); F. Santos, TOP 21 (2013), arXiv:1307.5900, Lemma 3.13 and Theorem 3.14.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk

open scoped RealInnerProductSpace

namespace Hirsch

theorem larman_layer_recursion (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hane : ∀ j, a j ≠ 0) (hbd : Bornology.IsBounded (Hpoly a b))
    (htight : ∀ v ∈ Set.extremePoints ℝ (Hpoly a b), ∃ j, ⟪a j, v⟫ = b j)
    (β : ℕ → ℕ) (Bd : ℕ)
    (hstep : ∀ u ∈ Set.extremePoints ℝ (Hpoly a b), ∀ (r : Fin n) (T : Finset (Fin n)), r ∈ T →
      ∀ y ∈ Set.extremePoints ℝ (Hpoly a b), ∀ z ∈ Set.extremePoints ℝ (Hpoly a b),
      ⟪a r, y⟫ = b r → ⟪a r, z⟫ = b r →
      (∀ j, ⟪a j, y⟫ = b j → j ∈ T) → (∀ j, ⟪a j, z⟫ = b j → j ∈ T) →
      (∀ w ∈ Set.extremePoints ℝ (Hpoly a b), ⟪a r, w⟫ = b r →
        (∃ j, j ∉ T ∧ ⟪a j, w⟫ = b j) → gdist (Hpoly a b) u w + 1 ≤ gdist (Hpoly a b) u y) →
      gdist (Hpoly a b) u z ≤ gdist (Hpoly a b) u y + β T.card)
    (harith : ∀ (k : ℕ) (m : Fin k → ℕ), (∀ i, 1 ≤ m i) →
      ∑ i, m i ≤ 2 * n → ∑ i, β (m i) + k ≤ Bd + 1) :
    DiamLE (Hpoly a b) Bd := by sorry

end Hirsch
