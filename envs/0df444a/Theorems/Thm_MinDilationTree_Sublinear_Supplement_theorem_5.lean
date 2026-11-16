-- Prove2me | Theorems.Thm_MinDilationTree_Sublinear_Supplement_theorem_5
-- name    : MinDilationTree.Sublinear.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:57:42.329866+00:00
-- url     : https://prove2.me/theorems/16a3127b-66ec-4a7c-b8a6-ecbc21159cc3
-- title:
--   Theorem 5 (Circle obstruction) — a disk of radius $R$ in a polygon of $\mathcal P_r$ forces $\mathrm{Opt}\ge 2R/r$
-- statement:
--   Let $S=\{p_0,\ldots,p_{n-1}\}$ be a set of distinct points in the plane, $D$ a Delaunay triangulation of $S$, and $r>0$. If some polygon $P$ of the $r$-support $\mathcal P_r(S)$ contains a disk of radius $R$, then
--   $$\mathrm{Opt}\ \ge\ \frac{2R}{r}.$$
--
--   In particular, if $S$ is not $\Lambda$-thin then $\mathrm{Opt}\ge2\Lambda$; this is the first of the two obstructions that the algorithm uses to certify a large optimum.
--
--   Differences from the source:
--   - reading: the Delaunay triangulation of S → every Delaunay triangulation D of S (an inclusion-maximal plane graph of empty-disk edges); the r-support and Λ-thinness are taken w.r.t. that D; reason: reading R1: the paper assumes no general position; in general position D is unique
--   - encoding: P_r: maximal weakly simple polygons bounded by the outer boundary walks of the components of the Delaunay triangulation after deleting edges longer than r → the closed regions K ∪ (bounded components of ℝ² \ K), K the embedded component, that are maximal under inclusion; reason: the region bounded by the outer boundary walk of a connected plane graph is exactly this set, and such a walk is always weakly simple; isolated points give the singleton polygons
--   - encoding: Opt and the bound as real numbers; the points as a set S → Opt and the bound in ℝ≥0∞ (the published opt of the live mission); S as an injective map Fin n → ℝ²; reason: finite trees on distinct points have finite dilation, so the values are unchanged
--   - encoding: a disk D(x, R) contained in P → Metric.closedBall x R ⊆ P; reason: P is closed, so it contains the open disk of radius R iff it contains the closed one
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 7 (PDF p. 8), Theorem 5

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_Supplement_Support

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- Theorem 5 (Circle obstruction), p.7 (PDF 8). For `r > 0` and every Delaunay triangulation `D`
(reading R1), if a polygon of the `r`-support contains a disk of radius `R`, then `Opt ≥ 2R/r`. -/
theorem theorem_5 {n : ℕ} (p : Fin n → Plane) (hp : Function.Injective p)
    (D : SimpleGraph (Fin n)) (hD : IsDelaunay p D) (r : ℝ) (hr : 0 < r)
    (P : Set Plane) (hP : P ∈ support p D r)
    (x : Plane) (R : ℝ) (hdisk : Metric.closedBall x R ⊆ P) :
    ENNReal.ofReal (2 * R / r) ≤ opt p := by sorry

end MinDilationTree.Sublinear.Supplement
