-- Prove2me | Theorems.Thm_MeasureTheory_eLpNorm_coordinate_evenReflection_le
-- name    : MeasureTheory.eLpNorm_coordinate_evenReflection_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T17:48:29.77276+00:00
-- url     : https://prove2.me/theorems/61b5fd0d-cd78-42e5-bb59-b42fb0509f22
-- title:
--   Uniform Lp seminorm bound for folding one Euclidean coordinate
-- statement:
--   Fix a coordinate $j$ and let $H=\{x:x_j>0\}$. If $g$ is almost everywhere strongly measurable on $H$ and $1\le p\le\infty$, its even reflection $Eg(x)=g(x_1,\ldots,|x_j|,\ldots,x_n)$ satisfies
--   $$\|Eg\|_{L^p(\mathbb R^n)}\le 2\|g\|_{L^p(H)}.$$
--   No integrability or weak differentiability assumption is needed. Arbitrary boundary values are harmless because $\{x_j=0\}$ has measure zero. The constant is uniform in $p$, including infinity. The proof writes the reflection almost everywhere as a zero extension plus its composition with a measure-preserving coordinate reflection, and uses the Lp triangle inequality.
-- source:
--   Auxiliary estimate for Hunter, Notes on Partial Differential Equations, revised 2014-06-18, §3.9, pp. 71–72, reflection construction preceding Theorem 3.41. https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . This arbitrary-function seminorm estimate is derived from measure preservation and Minkowski, not a separately numbered theorem in the source.

import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem MeasureTheory.eLpNorm_coordinate_evenReflection_le {n : ℕ} (j : Fin n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : AEStronglyMeasurable g (volume.restrict {x | 0 < x j})) :
    eLpNorm (fun x : EuclideanSpace ℝ (Fin n) =>
      g (WithLp.toLp 2 (fun i => if i = j then |x i| else x i))) p volume ≤
      2 * eLpNorm g p (volume.restrict {x | 0 < x j}) := by sorry
