-- Prove2me | Theorems.Thm_MinDilationTree_Sublinear_Supplement_lemma_4
-- name    : MinDilationTree.Sublinear.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:57:09.97487+00:00
-- url     : https://prove2.me/theorems/8628442d-4ef8-4f6f-8b6b-51b33c2b29f5
-- title:
--   Lemma 4 — a disk inside a weakly simple polygon on input points forces $\mathrm{Opt}\ge 2R/r$
-- statement:
--   Let $S=\{p_0,\ldots,p_{n-1}\}$ be a set of distinct points in the plane. Let $P$ be a weakly simple polygon with boundary walk $p_{i_1},\ldots,p_{i_m},p_{i_1}$ whose vertices are points of $S$ (repetitions allowed), and let
--   $$r=\max_{k}\|p_{i_k}-p_{i_{k+1}}\|$$
--   be its longest boundary edge, indices modulo $m$. If the disk $D(x,R)$ of centre $x$ and radius $R$ is contained in $P$, then
--   $$\mathrm{Opt}\ \ge\ \frac{2R}{r},$$
--   where $\mathrm{Opt}$ is the minimum dilation of a spanning tree of $S$.
--
--   This generalizes the circle lower bound of §3 to arbitrary weakly simple polygons; Theorem 5 applies it to the polygons of the $r$-support.
--
--   **Formalization Note** $2R/r$ is the quotient $\mathrm{ofReal}(2R)/\mathrm{ofReal}(r)$ in $[0,\infty]$. When $r=0$ the polygon is one point, so only $R\le0$ is possible and both sides are compared at $0$; when $R<0$ the disk is empty and the bound is $0$.
--
--   Differences from the source:
--   - reading: weakly simple polygon: (i) for every ε > 0 its vertices can be ε-perturbed to a simple polygon, (ii) its complement is path-connected; repeated visits are distinct vertices → a closed boundary walk whose ordered subdivision can be ε-perturbed to a simple polygon for every ε > 0, and whose closed region (the trace plus the points the walk winds around an odd number of times) has a path-connected complement; reason: the paper explicitly admits singletons and doubly traversed segments (p. 3, Figure 1), which have fewer than three vertices and cannot be perturbed vertex for vertex; subdividing an edge changes no polygon, and a walk perturbable as given uses the trivial subdivision
--   - encoding: Opt and the bound as real numbers; the points as a set S → Opt and the bound in ℝ≥0∞ (the published opt of the live mission); S as an injective map Fin n → ℝ²; reason: finite trees on distinct points have finite dilation, so the values are unchanged
--   - encoding: a disk D(x, R) contained in P → Metric.closedBall x R ⊆ P; reason: P is closed, so it contains the open disk of radius R iff it contains the closed one
--   - encoding: 2R/r → ENNReal.ofReal (2R) / ENNReal.ofReal r; reason: for r > 0 this is 2R/r; r = 0 occurs only for a one-point polygon, where only R ≤ 0 is possible and the bound is 0 ≤ Opt
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 6 (PDF p. 7), Lemma 4

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_Supplement_Polygon

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- Lemma 4, p.6 (PDF 7). A weakly simple polygon `P = p₁, …, p_m, p₁` whose boundary-walk vertices
are input points, with longest boundary edge `r`, that contains the disk `D(x, R)`, forces
`Opt ≥ 2R/r`. -/
theorem lemma_4 {n : ℕ} (p : Fin n → Plane) (hp : Function.Injective p)
    (W : BoundaryWalk) (hW : W.IsWeaklySimple) (hS : ∀ i, W.vertex i ∈ Set.range p)
    (x : Plane) (R : ℝ) (hdisk : Metric.closedBall x R ⊆ W.region) :
    ENNReal.ofReal (2 * R) / ENNReal.ofReal W.maxEdge ≤ opt p := by sorry

end MinDilationTree.Sublinear.Supplement
