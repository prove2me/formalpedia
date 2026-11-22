-- Prove2me | Theorems.Thm_MasulloGRH_realLocalZeta_meromorphic_and_residues
-- name    : MasulloGRH.realLocalZeta_meromorphic_and_residues
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:26.563878+00:00
-- url     : https://prove2.me/theorems/f7364875-2239-4792-a0dc-7960caf6d613
-- title:
--   Lemma 3.3.2.1 (real place), corrected — $Z_v(f,|\cdot|^s)$ and $Z_v(f,\mathrm{sgn}|\cdot|^s)$ are meromorphic with at most simple poles at $s=-m$ ($m$ even, resp. odd), of residue $2f^{(m)}(0)/m!$
-- statement:
--   **Poles and residues of the local zeta integrals at a real place** (Lemma 3.3.2.1, real case, of the source, with the corrected constant in the sign component).
--
--   Let $f\in\mathcal S(\mathbb R)$ be a Schwartz function. For $\operatorname{Re}s>0$ the local zeta integrals of $f$ on the two connected components of the quasi-characters of $\mathbb R^\times$ are the absolutely convergent integrals
--   $$Z(f,|\cdot|^s)=\int_{\mathbb R}f(x)\,|x|^{s-1}\,dx,\qquad Z(f,\mathrm{sgn}\,|\cdot|^s)=\int_{\mathbb R}f(x)\,\mathrm{sgn}(x)\,|x|^{s-1}\,dx$$
--   (integrals over $\mathbb R^\times$ for the measure $dx/|x|$). Then there are meromorphic functions $M_0$, $M_1$ on $\mathbb C$ such that:
--
--   1. $M_0(s)=Z(f,|\cdot|^s)$ and $M_1(s)=Z(f,\mathrm{sgn}\,|\cdot|^s)$ for $\operatorname{Re}s>0$;
--   2. $M_0$ is holomorphic outside the points $s=-m$ with $m\ge0$ even, and $M_1$ is holomorphic outside the points $s=-m$ with $m\ge1$ odd;
--   3. at these points the poles are at most simple, and for every even $m\ge0$, respectively every odd $m\ge1$,
--   $$\lim_{s\to-m}(s+m)\,M_0(s)=\frac{2\,f^{(m)}(0)}{m!},\qquad\text{respectively}\qquad\lim_{s\to-m}(s+m)\,M_1(s)=\frac{2\,f^{(m)}(0)}{m!}.$$
--
--   In the notation of the source the poles are at the quasi-characters $c_{0,m}(x)=|x|^{-m}$ and $c_{1,m}(x)=x^{-1}|x|^{-m}=\mathrm{sgn}(x)|x|^{-(m+1)}$, $m\in2\mathbb N$, and the residues are the distributions $\frac{2}{m!}\,\delta_0\circ\partial_x^{m}$, respectively $\frac{2}{(m+1)!}\,\delta_0\circ\partial_x^{m+1}$: the residues of the meromorphic family of homogeneous distributions $|x|^{s-1}$ and $\mathrm{sgn}(x)|x|^{s-1}$. The source uses them to describe the polar parts of the $S$-local $Z$-functions and the divisor of $L_S$.
--
--   **Deviation from the source.** With $D=\frac1{2\pi i}\partial_x$, formula (3.3.2.6)–(3.3.2.7) gives the residue $A_{v,0,m}D^m\delta_0=\frac{2}{m!}f^{(m)}(0)$ at $c_{0,m}$, as here, but $A_{v,1,m}D^{m+1}\delta_0=-\frac{2}{(m+1)!}f^{(m+1)}(0)$ at $c_{1,m}$: the sign is wrong. For $f(x)=xe^{-\pi x^2}$ one has $Z(f,\mathrm{sgn}|\cdot|^s)=\pi^{-(s+1)/2}\Gamma(\frac{s+1}2)$, with residue $+2=2f'(0)$ at $s=-1$.
--
--   **Formalization Note.** Pure Mathlib statement on `SchwartzMap ℝ ℂ`; $f^{(m)}(0)$ is `iteratedDeriv m f 0`; the residue is expressed by the limit of $(s+m)M(s)$ as $s\to-m$, $s\ne-m$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 138, Lemma 3.3.2.1(1)(1) and (2)(1), eqs. (3.3.2.2)–(3.3.2.3), (3.3.2.6)–(3.3.2.7) (proof pp. 139–140; the constant $A_{v,1,m}$ corrected); classical references cited in the proof: J. W. S. Cassels, A. Fröhlich (eds.), Algebraic Number Theory, Ch. XV (J. T. Tate, Fourier analysis in number fields and Hecke's zeta-functions), Theorem 2.4.1 and §2.5; G. B. Folland, Real Analysis, 2nd ed., Theorems 8.22(e) and 8.26

import Mathlib

open MeasureTheory
open scoped FourierTransform

set_option autoImplicit false

namespace MasulloGRH

theorem realLocalZeta_meromorphic_and_residues (f : SchwartzMap ℝ ℂ) :
    ∃ M₀ M₁ : ℂ → ℂ, MeromorphicOn M₀ Set.univ ∧ MeromorphicOn M₁ Set.univ ∧
      (∀ s : ℂ, 0 < s.re → M₀ s = ∫ x : ℝ, f x * ((|x| : ℝ) : ℂ) ^ (s - 1)) ∧
      (∀ s : ℂ, 0 < s.re →
        M₁ s = ∫ x : ℝ, f x * ((Real.sign x : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1)) ∧
      (∀ s : ℂ, (∀ m : ℕ, Even m → s ≠ -(m : ℂ)) → AnalyticAt ℂ M₀ s) ∧
      (∀ s : ℂ, (∀ m : ℕ, Odd m → s ≠ -(m : ℂ)) → AnalyticAt ℂ M₁ s) ∧
      (∀ m : ℕ, Even m →
        Filter.Tendsto (fun s : ℂ => (s + m) * M₀ s) (nhdsWithin (-(m : ℂ)) {-(m : ℂ)}ᶜ)
          (nhds (2 * iteratedDeriv m (fun x : ℝ => f x) 0 / (m.factorial : ℂ)))) ∧
      (∀ m : ℕ, Odd m →
        Filter.Tendsto (fun s : ℂ => (s + m) * M₁ s) (nhdsWithin (-(m : ℂ)) {-(m : ℂ)}ᶜ)
          (nhds (2 * iteratedDeriv m (fun x : ℝ => f x) 0 / (m.factorial : ℂ)))) := by sorry

end MasulloGRH
