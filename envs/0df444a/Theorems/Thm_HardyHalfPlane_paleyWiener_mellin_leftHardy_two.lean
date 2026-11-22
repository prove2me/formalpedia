-- Prove2me | Theorems.Thm_HardyHalfPlane_paleyWiener_mellin_leftHardy_two
-- name    : HardyHalfPlane.paleyWiener_mellin_leftHardy_two
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:48:56.288996+00:00
-- url     : https://prove2.me/theorems/c574bc53-ab38-4174-a6f5-047f9b418747
-- title:
--   Paley–Wiener, Mellin form: $M$ maps $\{u\in L^2(\mathbb R_{>0},t^{2b}dt/t):\operatorname{supp}u\subseteq[1,\infty)\}$ isometrically ($\times\sqrt{2\pi}$) onto $H^2(\mathbb C_{<b})$
-- statement:
--   **Paley–Wiener theorem for $H^2$ of a half-plane, Mellin form.** Let $b\in\mathbb R$. For a measurable $u\colon\mathbb R_{>0}\to\mathbb C$ put $\|u\|_b=\big(\int_0^\infty|u(t)|^2\,t^{2b}\,\frac{dt}{t}\big)^{1/2}$ (the norm of $L^2(\mathbb R_{>0},t^{2b}\,dt/t)$) and let $Mu(s)=\int_0^\infty u(t)\,t^{s}\,\frac{dt}{t}$ be its Mellin transform. Here $H^2(\mathbb C_{<a})$ is the Hardy space of the left half-plane $\mathbb C_{<a}=\{s\in\mathbb C:\operatorname{Re}s<a\}$: the holomorphic functions $\Phi$ on $\mathbb C_{<a}$ with finite norm $$\|\Phi\|_{H^2(\mathbb C_{<a})}=\sup_{\sigma<a}\Big(\int_{\mathbb R}|\Phi(\sigma+iy)|^2\,dy\Big)^{1/2}.$$
--   Then:
--   1. If $\|u\|_b<\infty$ and $u=0$ almost everywhere on $(0,1)$ (i.e. $u$ is supported in $[1,\infty)$), then $Mu(s)$ converges absolutely for every $s$ with $\operatorname{Re}s<b$, $Mu\in H^2(\mathbb C_{<b})$, and $$\|Mu\|_{H^2(\mathbb C_{<b})}=\sqrt{2\pi}\,\|u\|_b.$$
--   2. Conversely, for every $\Phi\in H^2(\mathbb C_{<b})$ there is such a $u$ (measurable, $\|u\|_b<\infty$, $u=0$ a.e. on $(0,1)$) with $\Phi(s)=Mu(s)$ for all $\operatorname{Re}s<b$.
--
--   So the Mellin transform is, up to the factor $\sqrt{2\pi}$, an isometric isomorphism from the functions of $L^2(\mathbb R_{>0},t^{2b}dt/t)$ supported in $[1,\infty)$ onto $H^2(\mathbb C_{<b})$; the factor reflects that the Plancherel measure of $dt/t$ is $dx/2\pi$. It is the classical Paley–Wiener theorem (`HardyHalfPlane.paleyWiener_laplace_memLeftHardy_two`, `HardyHalfPlane.paleyWiener_exists_laplace_of_memLeftHardy_two`) after the substitution $t=e^x$ and the shift $s\mapsto s-b$. In the source it is the case of the norm $\|\cdot\|_{b,0}$ of (9.2.1.2) alone (no logarithmic weights $(\log t)^k$) of the right-hand vertical arrow $M\colon M_{\rho_{1,+}}W^{2N,2}_b(\mathbb R_{>0})\to H^{2N,2}(\mathbb C_{<b})$ of diagram (9.2.1.6) in Theorem 9.2.1.2(3), and of the decomposition $M(\phi)=u_1+u_2$ of Corollary 9.2.1.3 (with $u_1=M(1_{[1,\infty)}\phi)\in H^{2N,2}(\mathbb C_{<b})$).
--
--   **Deviation from the source.** Theorem 9.2.1.2(3) calls the Mellin transform an isometric isomorphism onto $H^{2N,2}(\mathbb C_{<b})$. With the norms (9.2.1.2) and (9.2.2.1) of the source (no normalising constants) it is isometric only up to the factor $\sqrt{2\pi}$; this factor is stated here.
--
--   **Formalization Note.** The Mellin transform is Mathlib's `mellin u s` $=\int_{t>0}t^{s-1}u(t)\,dt$ and absolute convergence is `MellinConvergent u s`; $\|u\|_b^2$ is written as the lower Lebesgue integral $\int^-_{t>0}\|u(t)\|^2\,t^{2b-1}\,dt\in[0,\infty]$; the values of $u$ on $(-\infty,0]$ play no role. $H^2(\mathbb C_{<b})$ and its norm are the platform's `HardyHalfPlane.MemLeftHardy Φ b 2` and `HardyHalfPlane.leftHardyNorm Φ b 2`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 404–407, Theorem 9.2.1.2(2)–(3) (right-hand vertical arrow of diagram (9.2.1.6)) and Corollary 9.2.1.3, case of the norm $\|\cdot\|_{b,0}$ alone (no logarithmic weights); classical reference: P. Duren, Theory of $H^p$ Spaces, Academic Press, 1970, Ch. 11 (§11.2, Thm. 11.4, p. 192; §11.5, Corollary, p. 197); G. B. Folland, Real Analysis. Modern Techniques and Their Applications, 2nd ed., Wiley, 1999, Thm. 8.29 (Plancherel), both as cited by the paper in the proof of Theorem 9.2.1.2

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace HardyHalfPlane

theorem paleyWiener_mellin_leftHardy_two (b : ℝ) :
    (∀ u : ℝ → ℂ, AEStronglyMeasurable u (volume.restrict (Set.Ioi 0)) →
      (∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioo 0 1 → u t = 0) →
      (∫⁻ t in Set.Ioi 0, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * b - 1))) < ⊤ →
      (∀ s : ℂ, s.re < b → MellinConvergent u s) ∧
      HardyHalfPlane.MemLeftHardy (mellin u) b 2 ∧
      HardyHalfPlane.leftHardyNorm (mellin u) b 2 =
        ENNReal.ofReal (Real.sqrt (2 * Real.pi)) *
          (∫⁻ t in Set.Ioi 0, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * b - 1))) ^ (1 / 2 : ℝ)) ∧
    (∀ Φ : ℂ → ℂ, HardyHalfPlane.MemLeftHardy Φ b 2 →
      ∃ u : ℝ → ℂ, AEStronglyMeasurable u (volume.restrict (Set.Ioi 0)) ∧
        (∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioo 0 1 → u t = 0) ∧
        (∫⁻ t in Set.Ioi 0, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * b - 1))) < ⊤ ∧
        ∀ s : ℂ, s.re < b → Φ s = mellin u s) := by sorry

end HardyHalfPlane
