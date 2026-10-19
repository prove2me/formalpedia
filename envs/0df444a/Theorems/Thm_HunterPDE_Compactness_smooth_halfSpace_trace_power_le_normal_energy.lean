-- Prove2me | Theorems.Thm_HunterPDE_Compactness_smooth_halfSpace_trace_power_le_normal_energy
-- name    : HunterPDE.Compactness.smooth_halfSpace_trace_power_le_normal_energy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T09:41:14.679627+00:00
-- url     : https://prove2.me/theorems/bd82744f-2c75-41a4-9f62-e3d7d6749eae
-- title:
--   Smooth trace power bounded by the zeroth and normal derivative energies
-- statement:
--   Let $1\le p<\infty$ and let $f$ be smooth up to the boundary of the upper half-space, vanishing on the closed half-space outside an ambient compact set. Write $D_0 f$ and $D_n f$ for the chosen weak derivatives of orders zero and one in the normal direction. Then $$\|f(\cdot,0)\|_p^p\le p\bigl(\|D_0 f\|_p^p+\|D_n f\|_p^p\bigr),$$ where the two norms on the right use volume restricted to the open half-space. The bound is uniform in the dimension and includes $p=1$ and $m=0$. There is no boundary vanishing assumption. This is the anisotropic energy form of the smooth estimate in Hunter: the normal fundamental theorem estimate followed by Fubini, Hölder and Young inequalities. Identifying smooth classical derivatives with the chosen weak representatives is part of the assertion. Unlike a bound by the full Sobolev norm, this statement uses only the two indicated derivative energies.
-- source:
--   Derived anisotropic consequence of J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, Theorem 3.44 proof, printed p. 72, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf. Normal fundamental theorem, Fubini and Holder give boundary power <= p ||f||_p^(p-1)||partial_n f||_p; Young gives the displayed two-energy bound. At p=1 use the normal fundamental theorem directly.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.smooth_halfSpace_trace_power_le_normal_energy {m : ℕ}
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IsSmoothCompactClosedHalfSpace f) :
    eLpNorm (fun x' => f (boundaryPoint x')) p volume ^ p.toReal ≤
      ENNReal.ofReal p.toReal *
        (eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m) 0 f)
            p (volume.restrict (upperHalfSpace m)) ^ p.toReal +
          eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m)
            (Pi.single (Fin.last m) 1) f)
            p (volume.restrict (upperHalfSpace m)) ^ p.toReal) := by sorry
