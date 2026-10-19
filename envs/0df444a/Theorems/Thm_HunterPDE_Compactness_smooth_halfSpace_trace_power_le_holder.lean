-- Prove2me | Theorems.Thm_HunterPDE_Compactness_smooth_halfSpace_trace_power_le_holder
-- name    : HunterPDE.Compactness.smooth_halfSpace_trace_power_le_holder
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T13:49:44.518576+00:00
-- url     : https://prove2.me/theorems/1c10a6c3-8fc2-4456-8557-89984def5712
-- title:
--   Smooth half-space trace power bounded by the Holder product of its zero-order and normal-derivative energies
-- statement:
--   The $L^p$ power of the boundary restriction of a smooth half-space function is bounded by the Holder product of its zero-order $L^p$ energy and the $L^p$ energy of its normal weak derivative.
--
--   Let $m\ge0$, let $1\le p<\infty$, and let $H=\{x\in\mathbb{R}^{m+1}:x_{m+1}>0\}$ be the open upper half-space in dimension $m+1$. Let $f:\mathbb{R}^{m+1}\to\mathbb{R}$ be smooth up to the boundary of $H$ and vanish on the closed half-space outside an ambient compact set. Write $D_0f$ and $D_nf$ for the chosen weak derivatives of orders zero and one in the last (normal) coordinate, and identify $\partial H$ with $\mathbb{R}^m$ through $x'\mapsto(x',0)$. Then
--
--   $$\|f(\cdot,0)\|_p^p\le p\,\|D_0f\|_{L^p(H)}^{p-1}\,\|D_nf\|_{L^p(H)},$$
--
--   where both norms on the right use Lebesgue measure restricted to the open half-space, and the exponents $\frac{p-1}{p}$ and $\frac1p$ accompany the zero-order and normal-derivative energies respectively. The bound is uniform in the dimension and includes $p=1$ and $m=0$; no vanishing of $f$ on the boundary is assumed.
--
--   This is the first (Holder) half of the anisotropic smooth trace estimate that underlies Hunter's trace theorem for $W^{1,p}$ on the half-space, stated in the form in which it is combined with Young's inequality.
--
--   **Formalization Note** The weak derivatives are the chosen representatives `weakDeriv`; they agree almost everywhere with the classical derivatives of the smooth function. The boundary power and both energies are written with `eLpNorm` raised to the real exponent `p.toReal`.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, proof of Theorem 3.44, printed p. 72 (normal fundamental theorem, Fubini and Holder step). Anisotropic Holder form of the smooth trace estimate; it is the first half of the derivation of the two-energy bound.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.smooth_halfSpace_trace_power_le_holder {m : ℕ}
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IsSmoothCompactClosedHalfSpace f) :
    eLpNorm (fun x' => f (boundaryPoint x')) p volume ^ p.toReal ≤
      ENNReal.ofReal p.toReal *
        (eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m) 0 f)
            p (volume.restrict (upperHalfSpace m)) ^ p.toReal) ^ ((p.toReal - 1) / p.toReal) *
        (eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m)
            (Pi.single (Fin.last m) 1) f)
            p (volume.restrict (upperHalfSpace m)) ^ p.toReal) ^ (1 / p.toReal) := by sorry
