-- Prove2me | Theorems.Thm_MeasureTheory_mixed_green_identity_annulus
-- name    : MeasureTheory.mixed_green_identity_annulus
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-10T10:56:59.296222+00:00
-- url     : https://prove2.me/theorems/3b11ef73-ba7d-49cb-89ef-8dab4a34bbd2
-- title:
--   Mixed Green identity on a spherical annulus
-- statement:
--   Let $n\ge1$, let $K:\mathbb R^n\to\mathbb R$ be smooth away from the origin, and let $g:\mathbb R^n\to\mathbb R$ be $C^2$. Fix $x\in\mathbb R^n$, coordinate indices $i,j$, and $0<r<R$. Put
--
--   $$A=B_R(x)\setminus\overline B_r(x),$$
--
--   and define the surface expression
--
--   $$H_s(K,g)=\int_{S^{n-1}}\left[K(-s\omega)\partial_jg(x+s\omega)\omega_i+\partial_iK(-s\omega)g(x+s\omega)\omega_j\right]dS(\omega).$$
--
--   Then
--
--   $$\int_A\partial_{ij}K(x-y)g(y)\,dy=\int_AK(x-y)\partial_{ij}g(y)\,dy-R^{n-1}H_R(K,g)+r^{n-1}H_r(K,g).$$
--
--   The outer normal of the annulus is $\omega$ on the outer sphere and $-\omega$ on the inner sphere. The formula follows by integrating the mixed Green differential identity twice; smoothness permits the interchange of mixed derivatives. No compact support, radiality, harmonicity, or growth assumption is required. All evaluation points of the kernel on the closed annulus avoid the origin. The derivatives are coordinate Fréchet derivatives, and $dS$ is the surface measure induced by Lebesgue volume.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed pp. 37–38, differential identity preceding Eq. (2.27) and Green integration in (2.27). General smooth-kernel formulation on a spherical annulus; boundary surface measure is parametrized by the unit sphere.

import Definitions.Def_HunterPDE_Newtonian_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff

theorem MeasureTheory.mixed_green_identity_annulus
    (n : ℕ) (hn : 0 < n) (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : ContDiffOn ℝ ∞ K {0}ᶜ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (x : EuclideanSpace ℝ (Fin n)) (R r : ℝ) (hR : 0 < R)
    (hr : 0 < r) (hrR : r < R) (i j : Fin n) :
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      secondPartial K i j (x - y) * g y) =
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      K (x - y) * secondPartial g i j y)
    - R ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        K (-(R • w.1)) * partialDeriv g j (x + R • w.1) * w.1 i
        + partialDeriv K i (-(R • w.1)) * g (x + R • w.1) * w.1 j
        ∂volume.toSphere)
    + r ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        K (-(r • w.1)) * partialDeriv g j (x + r • w.1) * w.1 i
        + partialDeriv K i (-(r • w.1)) * g (x + r • w.1) * w.1 j
        ∂volume.toSphere) := by sorry
