-- Prove2me | Theorems.Thm_HunterPDE_Compactness_classical_halfSpace_trace_power_le_lintegral
-- name    : HunterPDE.Compactness.classical_halfSpace_trace_power_le_lintegral
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T16:19:19.778988+00:00
-- url     : https://prove2.me/theorems/1761927c-6e65-4956-804e-7ad387047e23
-- title:
--   Integrated classical normal trace power estimate for C¹ functions
-- statement:
--   For real r ≥ 1, a real function f that is C¹ on the closed upper half-space and vanishes there outside a compact set satisfies
--
--   $$\int_{\mathbb R^m}|f(x',0)|^r\,dx'\le r\int_H |f(x)|^{r-1}|\partial_n f(x)|\,dx.$$
--
--   The derivatives in this statement are classical derivatives in the open half-space. Integrals take values in the extended nonnegative reals. This includes r=1 and m=0; f is unrestricted below the boundary. This estimate follows from the fundamental theorem on each normal ray, then Tonelli and the product-coordinate formula for Euclidean volume.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, proof of Theorem 3.44, printed p. 72 (normal fundamental theorem, Fubini and Holder step). Anisotropic Holder form of the smooth trace estimate; it is the first half of the derivation of the two-energy bound. Here only C¹ regularity is assumed; this is the regularity used in the normal-ray argument.

import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
open MeasureTheory HunterPDE.Compactness HunterPDE.Shared
open scoped ENNReal NNReal ContDiff
set_option autoImplicit false

theorem HunterPDE.Compactness.classical_halfSpace_trace_power_le_lintegral {m : ℕ} (r : ℝ) (hr : 1 ≤ r)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : ContDiffOn ℝ 1 f (closedUpperHalfSpace m))
    (hK : ∃ K : Set (EuclideanSpace ℝ (Fin (m + 1))), IsCompact K ∧
      ∀ x ∈ closedUpperHalfSpace m, x ∉ K → f x = 0) :
    (∫⁻ x', ‖f (boundaryPoint x')‖ₑ ^ r) ≤ ENNReal.ofReal r *
      ∫⁻ x, ‖f x‖ₑ ^ (r - 1) * ‖partialDeriv f (Fin.last m) x‖ₑ
        ∂volume.restrict (upperHalfSpace m) := by sorry
