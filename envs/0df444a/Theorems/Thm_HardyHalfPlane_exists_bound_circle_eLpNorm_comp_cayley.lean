-- Prove2me | Theorems.Thm_HardyHalfPlane_exists_bound_circle_eLpNorm_comp_cayley
-- name    : HardyHalfPlane.exists_bound_circle_eLpNorm_comp_cayley
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T19:26:03.261236+00:00
-- url     : https://prove2.me/theorems/46b35d8a-f7c3-4eee-872b-9f141d50bdcf
-- title:
--   Composition with a Möbius map of the unit disc onto $\mathbf C_{<a}$ sends $H^p(\mathbf C_{<a})$ into $H^p$ of the unit disc
-- statement:
--   **Hardy functions of a half-plane transplanted to the unit disc.** Let $a\in\mathbb R$, let $0<p\le\infty$, and let $\Phi\in H^p(\mathbf C_{<a})$: the function $\Phi$ is holomorphic on the half-plane $\mathbf C_{<a}=\{s\in\mathbb C:\operatorname{Re}(s)<a\}$ and
--
--   $$\|\Phi\|_{H^p(\mathbf C_{<a})}=\sup_{\sigma<a}\Bigl(\int_{\mathbb R}|\Phi(\sigma+iy)|^p\,\mathrm dy\Bigr)^{1/p}<\infty$$
--
--   (for $p=\infty$ the $L^p$ norm on each line is replaced by the essential supremum, $\sup_{\sigma<a}\operatorname{ess\,sup}_{y\in\mathbb R}|\Phi(\sigma+iy)|<\infty$, i.e. $\Phi$ is bounded on $\mathbf C_{<a}$).
--
--   The Möbius transformation
--
--   $$w\longmapsto a+\frac{w+1}{w-1}$$
--
--   maps the unit disc $\mathbb D=\{|w|<1\}$ conformally onto $\mathbf C_{<a}$ (with $0\mapsto a-1$, and the unit circle minus the point $1$ onto the line $\operatorname{Re}(s)=a$). Let $F(w)=\Phi\bigl(a+\frac{w+1}{w-1}\bigr)$ on $\mathbb D$. Then $F$ belongs to the Hardy space $H^p(\mathbb D)$ of the disc: its integral means are bounded,
--
--   $$\sup_{0<r<1}\Bigl(\int_0^{2\pi}\Bigl|\Phi\Bigl(a+\frac{re^{i\theta}+1}{re^{i\theta}-1}\Bigr)\Bigr|^p\,\mathrm d\theta\Bigr)^{1/p}<\infty$$
--
--   (for $p=\infty$ the integral mean is replaced by the essential supremum in $\theta$, and the statement says that a bounded $\Phi$ gives a bounded $F$).
--
--   This is the classical comparison between the Hardy spaces of a half-plane and of the disc (P. Duren, *Theory of $H^p$ Spaces*, Ch. 11, in the normalisation of the upper half-plane): plain composition with a conformal map from the disc onto the half-plane sends $H^p$ of the half-plane into $H^p$ of the disc (for $p<\infty$ the converse fails: nonzero constants lie in $H^p(\mathbb D)$ but not in $H^p(\mathbf C_{<a})$). It allows boundary-value theorems for $H^p(\mathbb D)$ to be applied to $H^p(\mathbf C_{<a})$; the source uses the resulting boundary function $f_\Phi$ of $\Phi\in H^p(\mathbf C_{<a})$ in §B.2.1.
--
--   **Formalization Note.** `HardyHalfPlane.MemLeftHardy Φ a p` is the membership predicate of the accompanying definition file (holomorphy on `{s | s.re < a}` and finiteness of `leftHardyNorm Φ a p`). The exponent is `p : ℝ≥0∞` with `p ≠ 0`; the case `p = ⊤` is included. The integral mean on the circle of radius `r` is Mathlib's `eLpNorm` of `θ ↦ F (circleMap 0 r θ)` with respect to Lebesgue measure on $(0,2\pi]$, and the conclusion asks for one finite bound `C : ℝ≥0∞` valid for all `0 < r < 1`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 592, §B.2.1 (existence almost everywhere and $L^p$-membership of the boundary function $f_\Phi$, recalled from [Dur, Cor. to Thm. 11.1]); auxiliary lemma for the proof of HardyHalfPlane.exists_boundary_function; classical reference: P. Duren, Theory of $H^p$ Spaces, Academic Press, 1970, Chapter 11 ($H^p$ spaces over a half-plane)

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace HardyHalfPlane

theorem exists_bound_circle_eLpNorm_comp_cayley (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp0 : p ≠ 0)
    (hΦ : MemLeftHardy Φ a p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ r : ℝ, 0 < r → r < 1 →
      eLpNorm (fun θ : ℝ => Φ ((a : ℂ) + (circleMap 0 r θ + 1) / (circleMap 0 r θ - 1))) p
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) ≤ C := by sorry

end HardyHalfPlane
