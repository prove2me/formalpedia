-- Prove2me | Theorems.Thm_Hirsch_relaxation_no_new_neighbours
-- name    : Hirsch.relaxation_no_new_neighbours
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:03:23.785386+00:00
-- url     : https://prove2.me/theorems/ea856292-e347-4268-9e3c-7f590487e10a
-- title:
--   Dropping untouched inequalities creates no new neighbours
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$, let $F\subseteq\{1,\dots,n\}$, and let $P_F$ be the polyhedron cut out by the inequalities indexed by $F$ alone, so that $P\subseteq P_F$. Let $x$ be a vertex of $P$ and suppose
--
--   $$\{i:\langle a_i,x\rangle=b_i\}\subseteq F,\qquad \{i:\langle a_i,w\rangle=b_i\}\subseteq F\ \text{ for every neighbour } w \text{ of } x \text{ in } P.$$
--
--   Then every neighbour of $x$ in $P_F$ already lies in $P$. Since a vertex of $P$ whose tight inequalities lie in $F$ is still a vertex of $P_F$, this says the vertex figure at $x$ is unchanged by the relaxation, so no shortcut out of $x$ appears in $P_F$.
--
--   This is the step Kalai and Kleitman use to bound the radius of a layer around a vertex by the diameter of the polyhedron defined by the at most $\lfloor n/2\rfloor$ inequalities that layer touches. No simplicity or general-position hypothesis is needed.
--
--   **Formalization note.** The relaxed polyhedron is written by replacing each deleted row by the vacuous inequality $\langle 0,x\rangle\le 1$, which keeps the index set $\{1,\dots,n\}$ fixed.
-- source:
--   G. Kalai and D. J. Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. Amer. Math. Soc. 26 (1992), 315-316, p. 2 (proof of Theorem 1); M. J. Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, https://arxiv.org/abs/1402.3579, p. 2 (proof of Lemma 1)

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem relaxation_no_new_neighbours (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (F : Finset (Fin n)) (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Set.extremePoints ℝ (Hpoly a b))
    (hFx : ∀ i : Fin n, ⟪a i, x⟫ = b i → i ∈ F)
    (hadj : Adj (Hpoly (fun i => if i ∈ F then a i else 0)
      (fun i => if i ∈ F then b i else 1)) x y)
    (hnb : ∀ w, Adj (Hpoly a b) x w → ∀ i : Fin n, ⟪a i, w⟫ = b i → i ∈ F) :
    y ∈ Hpoly a b := by sorry

end Hirsch
