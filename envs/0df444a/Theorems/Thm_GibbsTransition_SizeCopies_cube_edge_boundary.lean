-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_cube_edge_boundary
-- name    : GibbsTransition.SizeCopies.cube_edge_boundary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:51:36.423303+00:00
-- url     : https://prove2.me/theorems/c5e3e80d-bae4-4573-9b34-19ec621269d9
-- title:
--   Lemma 4.1 — Edge boundary of a subset of the cube
-- statement:
--   Let $L\ge1$ and let $S$ be a nonempty subset of the cubic lattice box $\Lambda_L$. Its boundary $\partial S$ consists of nearest-neighbour edges from $S$ to its complement in the infinite cubic lattice. Then
--
--   $$|\partial S|\ge\frac{6|S|}{L},\qquad |\partial S|=\frac{6|S|}{L}\iff S=\Lambda_L.$$
--
--   The equality characterization and exterior edges are part of the statement. The bound controls the surface penalty in the ferromagnetic construction.
--
--   Differences from the source:
--   - encoding: sites in {1,…,L}³ → sites in Fin 3 → Fin L, with positively oriented integer-coordinate boundary edges; reason: translation by one and a unique orientation preserve all sites and unoriented edge counts
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Lemma 4.1, Equation (17), printed p. 7 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Lattice

namespace GibbsTransition.SizeCopies

/-- Lemma 4.1, printed p.7 (PDF p.9). Exterior edges are counted. -/
theorem cube_edge_boundary (L : ℕ) (hL : 1 ≤ L) (S : Finset (Site L))
    (hS : S.Nonempty) :
    (6 * (S.card : ℝ) / (L : ℝ) ≤ ((edgeBoundary S).card : ℝ)) ∧
    (((edgeBoundary S).card : ℝ) = 6 * (S.card : ℝ) / (L : ℝ) ↔
      S = Finset.univ) := by sorry

end GibbsTransition.SizeCopies
