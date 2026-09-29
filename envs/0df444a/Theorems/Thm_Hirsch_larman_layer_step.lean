-- Prove2me | Theorems.Thm_Hirsch_larman_layer_step
-- name    : Hirsch.larman_layer_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:49:06.197966+00:00
-- url     : https://prove2.me/theorems/693af58a-6379-4ddb-a07a-0d145cdb648b
-- title:
--   Larman's layer step: a facet relaxed to the rows of a distance layer creates no shortcuts
-- statement:
--   Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i<n\}$ be a bounded H-polytope, fix a base vertex $u$ and write $\rho(\cdot)=\mathrm{gdist}_P(u,\cdot)$ for the graph distance from $u$ (definition `Hirsch_walk`). Let $r$ be a row with $a_r\ne0$, let $T$ be a set of rows containing $r$, and suppose (inductive hypothesis) that every bounded H-polyhedron in $\mathbb{R}^{d-1}$ described by $|T|$ inequalities has diameter at most $B$. Let $y,z$ be vertices of $P$ on the facet $F_r=\{x\in P:\langle a_r,x\rangle=b_r\}$ whose tight rows all lie in $T$, and assume the **layer condition**: every vertex $w$ of $P$ on $F_r$ at which some row outside $T$ is tight lies strictly closer to $u$ than $y$,
--
--   $$\rho(w)+1\ \le\ \rho(y).$$
--
--   Then
--
--   $$\rho(z)\ \le\ \rho(y)+B .$$
--
--   This is the inductive step of Larman's proof of $\Delta(d,n)\le 2^{d-3}n$ in the form given by Kim--Santos: the facet $F_r$, relaxed to the inequalities active in the current distance layer (and bounded by one auxiliary cut, `Hirsch.bounded_relaxation_cut`), is a $(d-1)$-polyhedron with $|T|$ inequalities, so its vertices $y,z$ are joined by a walk of $B$ steps there. Followed **backwards from $z$**, that walk cannot leave $P$: as long as it stays at distance $\ge\rho(y)+1$ from $u$, every neighbour of the current vertex on $F_r$ is at distance $\ge\rho(y)$, hence has all its rows in $T$ by the layer condition, so by `Hirsch.relaxation_exit_vertex` the next step is an edge of $P$. Consequently the walk is a walk in $P$ and $\rho(z)\le\rho(y)+B$.
--
--   **Formalization Note** $T$ is a `Finset (Fin n)`; the inductive hypothesis is stated with exactly `T.card` inequalities in `EuclideanSpace ℝ (Fin (d-1))` and no nonemptiness hypothesis (the empty polytope satisfies every `DiamLE`). The direction of the walk (from $z$ towards $y$) is what makes the layer condition, which only constrains vertices *closer* than $y$, sufficient.
-- source:
--   D. G. Larman, Paths on polytopes, Proc. London Math. Soc. s3-20 (1970) 161-178, https://doi.org/10.1112/plms/s3-20.2.249; exposition followed: E. D. Kim, F. Santos, Companion to 'An update on the Hirsch conjecture', arXiv:0912.4235, Section 2.2, proof of Theorem 2.5 (layer decomposition, 'no facet is active in more than two V_i's', sum n_i <= 2n); F. Santos, TOP 21 (2013), arXiv:1307.5900, Lemma 3.13 and Theorem 3.14. The no-shortcut mechanism is that of Kalai--Kleitman's Lemma (G. Kalai, D. J. Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. AMS 26 (1992) 315-316, proof of the Lemma (the relaxed polyhedron cut out by the touched facets has no shorter paths), https://arxiv.org/abs/math/9204233; M. J. Todd, arXiv:1402.3579, Lemma 1.).

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk

open scoped RealInnerProductSpace

namespace Hirsch

theorem larman_layer_step (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (r : Fin n) (har : a r ≠ 0) (T : Finset (Fin n)) (hrT : r ∈ T) (B : ℕ)
    (IH : ∀ (a' : Fin T.card → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin T.card → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    (y z : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ Set.extremePoints ℝ (Hpoly a b)) (hz : z ∈ Set.extremePoints ℝ (Hpoly a b))
    (hyr : ⟪a r, y⟫ = b r) (hzr : ⟪a r, z⟫ = b r)
    (hyT : ∀ j, ⟪a j, y⟫ = b j → j ∈ T) (hzT : ∀ j, ⟪a j, z⟫ = b j → j ∈ T)
    (hback : ∀ w ∈ Set.extremePoints ℝ (Hpoly a b), ⟪a r, w⟫ = b r →
      (∃ j, j ∉ T ∧ ⟪a j, w⟫ = b j) → gdist (Hpoly a b) u w + 1 ≤ gdist (Hpoly a b) u y) :
    gdist (Hpoly a b) u z ≤ gdist (Hpoly a b) u y + B := by sorry

end Hirsch
