-- Prove2me | Theorems.Thm_HardyHalfPlane_paleyWiener_exists_laplace_of_memLeftHardy_two
-- name    : HardyHalfPlane.paleyWiener_exists_laplace_of_memLeftHardy_two
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:48:52.157391+00:00
-- url     : https://prove2.me/theorems/518e4039-84f6-4133-8eab-8eb172b88697
-- title:
--   Paley–Wiener: every $\Phi\in H^2(\mathbb C_{<0})$ is $\Phi(s)=\int_0^\infty f(x)e^{sx}\,dx$ with $f\in L^2(0,\infty)$
-- statement:
--   **Paley–Wiener theorem for $H^2$ of a half-plane: every $H^2$ function is the Laplace transform of an $L^2(0,\infty)$ function.** Here $H^2(\mathbb C_{<a})$ is the Hardy space of the left half-plane $\mathbb C_{<a}=\{s\in\mathbb C:\operatorname{Re}s<a\}$: the holomorphic functions $\Phi$ on $\mathbb C_{<a}$ with finite norm $$\|\Phi\|_{H^2(\mathbb C_{<a})}=\sup_{\sigma<a}\Big(\int_{\mathbb R}|\Phi(\sigma+iy)|^2\,dy\Big)^{1/2}.$$
--   Let $\Phi\in H^2(\mathbb C_{<0})$. Then there is $f\in L^2(\mathbb R)$ (complex-valued) with $f=0$ almost everywhere on $(-\infty,0)$ such that
--   $$\Phi(s)=\int_0^\infty f(x)\,e^{sx}\,dx\qquad\text{for every }s\text{ with }\operatorname{Re}s<0.$$
--
--   This is the surjectivity half of the classical Paley–Wiener theorem; the other half, `HardyHalfPlane.paleyWiener_laplace_memLeftHardy_two`, shows that $f\mapsto\Phi$ maps $L^2(0,\infty)$ isometrically (up to the factor $\sqrt{2\pi}$) into $H^2(\mathbb C_{<0})$, so $f$ is unique up to null sets. In the upper half-plane formulation: every $F\in H^2(\mathbb C_{\operatorname{Im}>0})$ is $F(z)=\int_0^\infty f(t)e^{itz}\,dt$ with $f\in L^2(0,\infty)$. In the source this is the step of the proof of Theorem 9.2.1.2(3) (p. 406) showing that the Mellin anti-transform of an element of the Hardy space of a half-plane is supported in a half-line.
--
--   **Formalization Note.** $H^2(\mathbb C_{<0})$ is the platform's `HardyHalfPlane.MemLeftHardy Φ 0 2`; only the values of $\Phi$ on $\operatorname{Re}s<0$ are constrained. The integral is a Bochner integral over $\mathbb R$; it converges absolutely for $\operatorname{Re}s<0$ by the companion theorem, so no junk value is involved.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 406, proof of Theorem 9.2.1.2(3) (support of the Mellin anti-transform of an element of a half-plane Hardy space); classical reference: P. Duren, Theory of $H^p$ Spaces, Academic Press, 1970, Ch. 11 (§11.2, Thm. 11.4, p. 192; §11.5, Corollary, p. 197), as cited by the paper in that proof

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace HardyHalfPlane

theorem paleyWiener_exists_laplace_of_memLeftHardy_two (Φ : ℂ → ℂ)
    (hΦ : HardyHalfPlane.MemLeftHardy Φ 0 2) :
    ∃ f : ℝ → ℂ, MemLp f 2 volume ∧ (∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0) ∧
      ∀ s : ℂ, s.re < 0 → Φ s = ∫ x : ℝ, f x * Complex.exp (s * x) := by sorry

end HardyHalfPlane
