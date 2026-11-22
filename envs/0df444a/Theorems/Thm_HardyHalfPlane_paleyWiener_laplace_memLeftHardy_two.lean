-- Prove2me | Theorems.Thm_HardyHalfPlane_paleyWiener_laplace_memLeftHardy_two
-- name    : HardyHalfPlane.paleyWiener_laplace_memLeftHardy_two
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:48:52.432752+00:00
-- url     : https://prove2.me/theorems/e4b5e072-44d0-4aab-a39b-01477438544c
-- title:
--   Paley–Wiener: the Laplace transform of $f\in L^2(0,\infty)$ lies in $H^2(\mathbb C_{<0})$ with $\|\Phi\|_{H^2}=\sqrt{2\pi}\,\|f\|_{L^2}$
-- statement:
--   **Paley–Wiener theorem for $H^2$ of a half-plane: the Laplace transform of $L^2(0,\infty)$ is isometric into $H^2$.** Let $f\in L^2(\mathbb R)$ (complex-valued) vanish almost everywhere on $(-\infty,0)$, and put
--   $$\Phi(s)=\int_0^\infty f(x)\,e^{sx}\,dx\qquad(\operatorname{Re}s<0).$$
--   Here $H^2(\mathbb C_{<a})$ is the Hardy space of the left half-plane $\mathbb C_{<a}=\{s\in\mathbb C:\operatorname{Re}s<a\}$: the holomorphic functions $\Phi$ on $\mathbb C_{<a}$ with finite norm $$\|\Phi\|_{H^2(\mathbb C_{<a})}=\sup_{\sigma<a}\Big(\int_{\mathbb R}|\Phi(\sigma+iy)|^2\,dy\Big)^{1/2}.$$
--   Then:
--   1. for every $s$ with $\operatorname{Re}s<0$ the integral defining $\Phi(s)$ converges absolutely;
--   2. $\Phi\in H^2(\mathbb C_{<0})$;
--   3. $\|\Phi\|_{H^2(\mathbb C_{<0})}=\sqrt{2\pi}\,\|f\|_{L^2(\mathbb R)}$.
--
--   Together with its converse `HardyHalfPlane.paleyWiener_exists_laplace_of_memLeftHardy_two` this is the classical Paley–Wiener theorem: $f\mapsto\Phi$ is, up to the factor $\sqrt{2\pi}$, an isometric isomorphism of $L^2(0,\infty)$ onto $H^2(\mathbb C_{<0})$. (In the usual formulation on the upper half-plane, $F(z)=\int_0^\infty f(t)e^{itz}\,dt$; the substitution $s=iz$ turns the upper half-plane into $\mathbb C_{<0}$.) In the source it is the classical input of Theorem 9.2.1.2(3) and Corollary 9.2.1.3: under the Mellin transform, functions on $\mathbb R_{>0}$ supported in a half-line correspond to Hardy-space functions on a half-plane (the right-hand vertical arrow of diagram (9.2.1.6)); see also the Mellin form `HardyHalfPlane.paleyWiener_mellin_leftHardy_two`.
--
--   **Formalization Note.** $H^2(\mathbb C_{<0})$ and its norm are the platform's `HardyHalfPlane.MemLeftHardy Φ 0 2` and `HardyHalfPlane.leftHardyNorm Φ 0 2` (values in $[0,\infty]$); $\|f\|_{L^2}$ is Mathlib's `eLpNorm f 2 volume`. The support condition is stated almost everywhere. $\Phi(s)$ is written as a Bochner integral over $\mathbb R$, which equals the integral over $(0,\infty)$ because $f=0$ a.e. on $(-\infty,0)$; absolute convergence is part of the conclusion, so the junk value of a non-integrable Bochner integral plays no role.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 405–407, Theorem 9.2.1.2(3) (diagram (9.2.1.6)) and its proof, and Corollary 9.2.1.3; classical reference: P. Duren, Theory of $H^p$ Spaces, Academic Press, 1970, Ch. 11 (§11.2, Thm. 11.4, p. 192; §11.5, Corollary, p. 197); G. B. Folland, Real Analysis. Modern Techniques and Their Applications, 2nd ed., Wiley, 1999, Thm. 8.29 (Plancherel), both as cited by the paper in the proof of Theorem 9.2.1.2

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace HardyHalfPlane

theorem paleyWiener_laplace_memLeftHardy_two (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hf0 : ∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0) :
    (∀ s : ℂ, s.re < 0 → Integrable (fun x : ℝ => f x * Complex.exp (s * x)) volume) ∧
    HardyHalfPlane.MemLeftHardy (fun s : ℂ => ∫ x : ℝ, f x * Complex.exp (s * x)) 0 2 ∧
    HardyHalfPlane.leftHardyNorm (fun s : ℂ => ∫ x : ℝ, f x * Complex.exp (s * x)) 0 2 =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi)) * eLpNorm f 2 volume := by sorry

end HardyHalfPlane
