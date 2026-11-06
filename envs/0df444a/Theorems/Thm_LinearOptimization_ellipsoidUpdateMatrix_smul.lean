-- Prove2me | Theorems.Thm_LinearOptimization_ellipsoidUpdateMatrix_smul
-- name    : LinearOptimization.ellipsoidUpdateMatrix_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:16:24.266047+00:00
-- url     : https://prove2.me/theorems/6e48a592-33e3-4150-8cfb-167b56a166ac
-- title:
--   Ellipsoid matrix update is invariant under rescaling the cut
-- statement:
--   **The ellipsoid matrix update is invariant under positive rescaling of the violated constraint.**
--
--   The update is
--   $$D' \;=\; \frac{n^2}{n^2-1}\Big(D-\frac{2}{n+1}\,\frac{Daa^{\mathsf T}D}{a^{\mathsf T}Da}\Big).$$
--   Under $a\mapsto ca$, $c>0$: the rank-one matrix $Daa^{\mathsf T}D$ scales by $c^2$ and the denominator $a^{\mathsf T}Da$ scales by $c^2$, so their ratio is unchanged; the prefactor does not involve $a$.
--
--   **Consequence.** Together with the centre-update invariance, this means the whole ellipsoid trajectory depends on the cut only through its direction. A rational implementation can therefore replace every cut by a positive rational multiple, keeping all arithmetic exact.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Theorem 8.1, p. 371, step (d); the invariance that permits exact rational arithmetic in the ellipsoid method.

import Mathlib
import Definitions.Def_LinearOptimization_EllipsoidMethod

open Matrix
open scoped BigOperators

namespace LinearOptimization

/-- **The matrix update is invariant under positive rescaling of the cut.** -/
theorem ellipsoidUpdateMatrix_smul {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    {c : ℝ} (hc : 0 < c) :
    ellipsoidUpdateMatrix D (c • a) = ellipsoidUpdateMatrix D a := by sorry

end LinearOptimization
