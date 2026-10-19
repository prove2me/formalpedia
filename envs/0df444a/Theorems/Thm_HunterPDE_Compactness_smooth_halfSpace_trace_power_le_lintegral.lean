-- Prove2me | Theorems.Thm_HunterPDE_Compactness_smooth_halfSpace_trace_power_le_lintegral
-- name    : HunterPDE.Compactness.smooth_halfSpace_trace_power_le_lintegral
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T14:43:05.018019+00:00
-- url     : https://prove2.me/theorems/5ca4cfff-ae14-4c98-9e99-35b4975e603e
-- title:
--   Normal fundamental-theorem bound for the smooth half-space boundary power
-- statement:
--   Let $m\ge 0$, $1\le p<\infty$, and let $f$ be smooth on the closed upper half-space and vanish there outside a compact set. With $D_0f$ and $D_nf$ the chosen zero-order and normal first weak derivatives, the boundary power satisfies
--
--   $$\|f(\cdot,0)\|_p^p\le p\int_H |D_0f|^{p-1}|D_nf|\,dx.$$
--
--   No boundary vanishing is assumed. The statement includes $p=1$ (the zero-order factor is then one) and $m=0$. This is the integrated normal fundamental-theorem estimate before applying Holder: integrate the one-dimensional bound along each inward normal ray, then apply Tonelli and the product-coordinate identification of Lebesgue measure. The weak representatives must be identified almost everywhere with the classical smooth derivatives. All integrals and powers in the formal statement take values in the extended nonnegative reals.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, proof of Theorem 3.44, printed p. 72 (normal fundamental theorem, Fubini and Holder step). Anisotropic Holder form of the smooth trace estimate; it is the first half of the derivation of the two-energy bound.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.smooth_halfSpace_trace_power_le_lintegral {m : ℕ}
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IsSmoothCompactClosedHalfSpace f) :
    eLpNorm (fun x' => f (boundaryPoint x')) p volume ^ p.toReal ≤
      ENNReal.ofReal p.toReal *
        ∫⁻ x, ‖HunterPDE.Shared.weakDeriv (upperHalfSpace m) 0 f x‖ₑ ^ (p.toReal - 1) *
          ‖HunterPDE.Shared.weakDeriv (upperHalfSpace m)
            (Pi.single (Fin.last m) 1) f x‖ₑ ∂volume.restrict (upperHalfSpace m) := by sorry
