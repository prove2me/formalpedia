-- Prove2me | Theorems.Thm_Hirsch_bounded_relaxation_cut
-- name    : Hirsch.bounded_relaxation_cut
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:48:36.464082+00:00
-- url     : https://prove2.me/theorems/b91b32f4-992f-4aa3-81c3-e64a9bab3da1
-- title:
--   A relaxation keeping the tight rows of a vertex becomes bounded after one auxiliary cut
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i<n\}$ be bounded, let $T$ be a set of row indices, and let $v$ be a vertex of $P$ all of whose tight inequalities have indices in $T$. Put $c=-\sum_{j\in T}a_j$. Then there is a real $M$ such that
--
--   $$\langle c,x\rangle\le M\quad\text{for all }x\in P,$$
--
--   and the polyhedron
--
--   $$R=\{x\in\mathbb{R}^d:\ \langle a_j,x\rangle\le b_j\ (j\in T),\ \ \langle c,x\rangle\le M\}$$
--
--   is bounded. Thus $P\subseteq R$, and $R$ is a bounded H-polytope described by $|T|+1$ inequalities.
--
--   The relaxation $\{x:\langle a_j,x\rangle\le b_j,\ j\in T\}$ is in general unbounded; the single cut $\langle c,x\rangle\le M$ bounds it because a direction $e$ with $\langle a_j,e\rangle\le0$ for all $j\in T$ and $-\sum_{j\in T}\langle a_j,e\rangle\le0$ must satisfy $\langle a_j,e\rangle=0$ for every $j\in T$, and the normals indexed by $T$ span $\mathbb{R}^d$ since they contain the tight normals of the vertex $v$. This is the device that lets a diameter induction apply its inductive hypothesis (stated for bounded polytopes) to Kalai--Kleitman or Larman relaxations.
--
--   **Formalization Note** The cut uses the specific normal $-\sum_{j\in T}a_j$, as in the platform proof of `Hirsch.graph_connected_general`.
-- source:
--   Cut construction as in Prove2Me Hirsch.graph_connected_general (8b17b820-f7a3-42e4-89a3-efd89fad4f3b); recession-cone characterisation of boundedness: Bertsimas--Tsitsiklis, Introduction to Linear Optimization, Theorem 4.14 and Section 4.7 (a polyhedron is bounded iff its recession cone is {0}). G. Kalai, D. J. Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. AMS 26 (1992) 315-316, proof of the Lemma (the relaxed polyhedron cut out by the touched facets has no shorter paths), https://arxiv.org/abs/math/9204233; M. J. Todd, arXiv:1402.3579, Lemma 1.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem bounded_relaxation_cut (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) (T : Finset (Fin n))
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hvT : ∀ j, ⟪a j, v⟫ = b j → j ∈ T) :
    ∃ M : ℝ, (∀ x ∈ Hpoly a b, ⟪-∑ j ∈ T, a j, x⟫ ≤ M) ∧
      Bornology.IsBounded {x : EuclideanSpace ℝ (Fin d) |
        (∀ j ∈ T, ⟪a j, x⟫ ≤ b j) ∧ ⟪-∑ j ∈ T, a j, x⟫ ≤ M} := by sorry

end Hirsch
