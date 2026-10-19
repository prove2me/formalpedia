-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_halfSpace_snoc
-- name    : MeasureTheory.lintegral_halfSpace_snoc
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T16:48:20.863982+00:00
-- url     : https://prove2.me/theorems/b92d01d6-70b0-410e-9ab5-f4947308fb41
-- title:
--   Tonelli formula for Euclidean upper half-space in boundary and normal coordinates
-- statement:
--   For any nonnegative extended-real function F that is almost everywhere measurable on the open upper half-space in dimension m+1,
--
--   $$\int_H F(x)\,dx=\int_{\mathbb R^m}\int_{(0,\infty)}F(x',t)\,dt\,dx'.$$
--
--   No finiteness assumption is required. The boundary dimension m may be zero, with its canonical Euclidean volume.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, proof of Theorem 3.44, printed p. 72 (normal fundamental theorem, Fubini and Holder step). Anisotropic Holder form of the smooth trace estimate; it is the first half of the derivation of the two-energy bound. Here only C¹ regularity is assumed; this is the regularity used in the normal-ray argument. Supporting interface: Tonelli and Euclidean boundary/normal coordinates.

import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory Set HunterPDE.Compactness
open scoped ENNReal
set_option autoImplicit false

theorem MeasureTheory.lintegral_halfSpace_snoc {m : ℕ} (F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞)
    (hF : AEMeasurable F (volume.restrict (upperHalfSpace m))) :
    (∫⁻ x, F x ∂volume.restrict (upperHalfSpace m)) =
      ∫⁻ x' : EuclideanSpace ℝ (Fin m), ∫⁻ t in Ioi (0 : ℝ),
        F (WithLp.toLp 2 (Fin.snoc (fun i => x' i) t)) := by sorry
