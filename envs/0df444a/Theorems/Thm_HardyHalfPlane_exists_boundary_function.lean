-- Prove2me | Theorems.Thm_HardyHalfPlane_exists_boundary_function
-- name    : HardyHalfPlane.exists_boundary_function
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T15:24:36.747701+00:00
-- url     : https://prove2.me/theorems/69f5d21f-d147-465f-92b1-9299d8e2e4e9
-- title:
--   Boundary values of $H^p$ functions on a half-plane exist almost everywhere and lie in $L^p$
-- statement:
--   **Boundary values of Hardy functions on a half-plane.** Let $a\in\mathbb R$, let $0<p<\infty$, and let $\Phi\in H^p(\mathbf C_{<a})$: the function $\Phi$ is holomorphic on the half-plane $\mathbf C_{<a}=\{s\in\mathbb C:\operatorname{Re}(s)<a\}$ and
--
--   $$\|\Phi\|_{H^p(\mathbf C_{<a})}=\sup_{\sigma<a}\Bigl(\int_{\mathbb R}|\Phi(\sigma+iy)|^p\,\mathrm dy\Bigr)^{1/p}<\infty .$$
--
--   Then the horizontal limit
--
--   $$f_\Phi(y):=\lim_{\sigma\to a^-}\Phi(\sigma+iy)$$
--
--   exists for Lebesgue-almost every $y\in\mathbb R$, and the boundary function $f_\Phi$ belongs to $L^p(\mathbb R,\mathrm dy)$.
--
--   Precisely: there is a function $g\in L^p(\mathbb R)$ such that $\Phi(\sigma+iy)\to g(y)$ as $\sigma\to a^-$ for almost every $y\in\mathbb R$.
--
--   This is the half-plane form of Fatou's theorem for Hardy spaces. The source recalls it in §B.2.1 (from Duren's book) to define the boundary map $\Phi\mapsto f_\Phi$ from $H^p(\mathbf C_{<a})$ to $L^p(\mathbb R)$ and to state the Cauchy integral formula on the boundary line $\operatorname{Re}(s)=a$.
--
--   **Formalization Note.** `HardyHalfPlane.MemLeftHardy Φ a p` is the membership predicate of the accompanying definition file, with exponent `p : ℝ≥0∞`; the hypotheses `p ≠ 0`, `p ≠ ⊤` encode $0<p<\infty$. The limit is taken along the filter `𝓝[<] a` of real numbers $\sigma$ tending to $a$ from the left, and `MemLp g p volume` includes almost-everywhere strong measurability of $g$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 592, §B.2.1 (existence almost everywhere and $L^p$-membership of the boundary function $f_\Phi$); classical reference: P. Duren, Theory of $H^p$ Spaces, Academic Press, 1970, Corollary to Theorem 11.1 (as cited by the paper at that spot)

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace HardyHalfPlane

theorem exists_boundary_function (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    (hΦ : MemLeftHardy Φ a p) :
    ∃ g : ℝ → ℂ, MemLp g p volume ∧
      ∀ᵐ y : ℝ ∂volume,
        Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a) (𝓝 (g y)) := by sorry

end HardyHalfPlane
