-- Prove2me | Theorems.Thm_HardyHalfPlane_eLpNorm_boundary_function_eq_leftHardyNorm
-- name    : HardyHalfPlane.eLpNorm_boundary_function_eq_leftHardyNorm
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T15:24:36.277534+00:00
-- url     : https://prove2.me/theorems/60642a8e-3a9d-4fad-9733-226ffccddb62
-- title:
--   The boundary function of $\Phi\in H^p(\mathbf C_{<a})$, $1\le p<\infty$, has $L^p$ norm $\|\Phi\|_{H^p}$
-- statement:
--   **The boundary map $H^p(\mathbf C_{<a})\to L^p(\mathbb R)$ is norm-preserving for $1\le p<\infty$.** Let $a\in\mathbb R$, let $1\le p<\infty$, and let $\Phi\in H^p(\mathbf C_{<a})$, the Hardy space of the half-plane $\mathbf C_{<a}=\{\operatorname{Re}(s)<a\}$ with norm
--
--   $$\|\Phi\|_{H^p(\mathbf C_{<a})}=\sup_{\sigma<a}\ \bigl\|\Phi(\sigma+i\,\cdot\,)\bigr\|_{L^p(\mathbb R,\mathrm dy)} .$$
--
--   Let $f_\Phi(y)=\lim_{\sigma\to a^-}\Phi(\sigma+iy)$ be its boundary function, which is defined for almost every $y\in\mathbb R$. Then
--
--   $$\|f_\Phi\|_{L^p(\mathbb R,\mathrm dy)}=\|\Phi\|_{H^p(\mathbf C_{<a})} .$$
--
--   Consequently the boundary map $\Phi\mapsto f_\Phi$ is an isometric embedding of $H^p(\mathbf C_{<a})$ into $L^p(\mathbb R,\mathrm dy)$. For instance, for $\Phi(s)=1/(s-1)$, $a=0$ and $p=2$ both sides are equal to $\sqrt\pi$.
--
--   The source recalls this in §B.2.1 (from Duren's book) to identify $H^p(\mathbf C_{<a})$, $p\ge1$, with a closed subspace of $L^p(\mathbb R)$; it is the half-plane counterpart of the identification of the Hardy space of the disc with a subspace of $L^p$ of the circle.
--
--   **Formalization Note.** The statement is given for an arbitrary function $g$ which is almost everywhere the limit of $\Phi(\sigma+iy)$ as $\sigma\to a^-$ (the boundary function is determined up to a null set; its existence is the companion statement `HardyHalfPlane.exists_boundary_function`). Norms are Mathlib's `eLpNorm` and the `ℝ≥0∞`-valued `HardyHalfPlane.leftHardyNorm`; the hypotheses `1 ≤ p`, `p ≠ ⊤` encode $1\le p<\infty$, the range in which the source asserts the equality.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 592, §B.2.1 (the boundary map $\Phi\mapsto f_\Phi$ is norm-preserving for $p\ge1$); classical reference: P. Duren, Theory of $H^p$ Spaces, Academic Press, 1970, Corollary to Theorem 11.2, p. 190 (as cited by the paper at that spot)

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace HardyHalfPlane

theorem eLpNorm_boundary_function_eq_leftHardyNorm (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞)
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hΦ : MemLeftHardy Φ a p) (g : ℝ → ℂ)
    (hg : ∀ᵐ y : ℝ ∂volume,
      Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a) (𝓝 (g y))) :
    eLpNorm g p volume = leftHardyNorm Φ a p := by sorry

end HardyHalfPlane
