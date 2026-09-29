-- Prove2me | Theorems.Thm_Hirsch_kalai_kleitman_recursion
-- name    : Hirsch.kalai_kleitman_recursion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:21:27.177636+00:00
-- url     : https://prove2.me/theorems/ceeb0d65-7515-467b-baad-2118ca9beaec
-- title:
--   The Kalai--Kleitman recursion $\Delta(d,n) \le \Delta(d-1,n-1) + 2\Delta(d,\lfloor n/2\rfloor) + 2$
-- statement:
--   Write $\Delta(d,n)$ for the largest combinatorial diameter of the vertex-edge graph of a $d$-dimensional polyhedron with $n$ facets. Kalai and Kleitman's key lemma is the recursion
--
--   $$\Delta(d,n)\ \le\ \Delta(d-1,n-1)\ +\ 2\,\Delta\bigl(d,\lfloor n/2\rfloor\bigr)\ +\ 2,$$
--
--   from which the quasi-polynomial bound $n^{\log_2 d+2}$ follows by induction on $d+n$.
--
--   This statement is that recursion in the form a diameter induction consumes it. Let $P$ be a bounded polytope in $\mathbb{R}^d$ cut out by $n$ inequalities $\langle a_i,x\rangle\le b_i$, all with $a_i\ne 0$, whose vertex-edge graph is connected. Suppose every bounded polyhedron in $\mathbb{R}^{d-1}$ with $n-1$ inequalities has diameter at most $B_1$, and every polyhedron cut out by at most $\lfloor n/2\rfloor$ of the inequalities of $P$ has diameter at most $B_2$. Then $P$ has diameter at most $2B_2+B_1+2$.
--
--   The proof splits on whether the balls around an endpoint eventually touch more than half of the inequalities. If they do for both endpoints, each reaches a half-cover within $B_2+1$ steps, the two half-covers must share an inequality, and crossing the facet it cuts out costs $B_1$. If they do not for some endpoint, the inequalities its balls touch already contain the tight sets of both endpoints, so the polyhedron cut out by those inequalities alone joins them in $B_2$ steps, and that walk lifts back into $P$ because relaxing untouched inequalities creates no shortcuts.
--
--   **Formalization note.** The relaxed polyhedron is written by replacing each deleted row by the vacuous inequality $\langle 0,x\rangle\le 1$, so that the index set stays $\{1,\dots,n\}$. The connectivity hypothesis is the statement that any two vertices are joined by some walk; it is a theorem for bounded polytopes and is taken as a hypothesis here so that the recursion can also be applied to unbounded relaxations.
-- source:
--   G. Kalai and D. J. Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. Amer. Math. Soc. 26 (1992), 315-316, p. 2 (proof of Theorem 1); M. J. Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, https://arxiv.org/abs/1402.3579, p. 2, Lemma 1

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem kalai_kleitman_recursion (d k : ℕ) (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (hane : ∀ i, a i ≠ 0)
    (hbd : Bornology.IsBounded (Hpoly a b)) (B₁ B₂ : ℕ)
    (IH1 : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B₁)
    (IH2 : ∀ F : Finset (Fin (k + 1)), F.card ≤ (k + 1) / 2 →
      DiamLE (Hpoly (fun i => if i ∈ F then a i else 0)
                    (fun i => if i ∈ F then b i else 1)) B₂)
    (hconn : ∀ u ∈ Set.extremePoints ℝ (Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hpoly a b),
      ∃ L, ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) :
    DiamLE (Hpoly a b) (2 * B₂ + B₁ + 2) := by sorry

end Hirsch
