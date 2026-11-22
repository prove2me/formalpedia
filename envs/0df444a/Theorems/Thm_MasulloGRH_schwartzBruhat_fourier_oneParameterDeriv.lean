-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_fourier_oneParameterDeriv
-- name    : MasulloGRH.schwartzBruhat_fourier_oneParameterDeriv
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:05.665636+00:00
-- url     : https://prove2.me/theorems/df656b7f-6144-45c8-a24b-a5258bb8c769
-- title:
--   Lemma D.1.6.19(1) — Fourier transform of a derivative on an LCA group: $\widehat{\partial_a f}(\chi)=p(\partial_a)(\chi)\,\widehat f(\chi)$ for $f\in\mathcal S(G)$
-- statement:
--   **The Fourier transform turns invariant differentiation into multiplication by the symbol** (Lemma D.1.6.19(1), with Definition D.1.6.10 and Lemma D.1.6.13).
--
--   Throughout, $G$ is a Hausdorff locally compact abelian group, written multiplicatively, and $\widehat G$ is its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$ with the compact-open topology). A closed subgroup $k\subseteq G$ is **good** if its annihilator $k^\perp=\{\chi\in\widehat G:\chi|_k=1\}$ is open and compactly generated in $\widehat G$ (then $k$ is compact). A pair $(\Gamma,k)$ of subgroups is **structural** if $\Gamma$ is open and compactly generated, $k$ is good and $k\subseteq\Gamma$; then $\Gamma/k$ is an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ ($F$ finite). $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ is the Fréchet space of functions on $G$ that vanish outside $\Gamma$, are $k$-invariant, and induce a smooth rapidly decreasing function on $\Gamma/k$. The **Schwartz–Bruhat space** is
--   $$\mathcal S(G)=\bigcup_{(\Gamma,k)}\mathcal S(k,\Gamma)$$
--   with the locally convex inductive limit topology (the finest locally convex topology making all inclusions $\mathcal S(k,\Gamma)\to\mathcal S(G)$ continuous).
--
--   Fix a Haar measure $\mu$ on $G$ and write $\widehat f(\chi)=\int_G f(x)\overline{\chi(x)}\,d\mu(x)$ for the Fourier transform. Let $a\colon\mathbb R\to G$ be a one-parameter subgroup (a continuous homomorphism) and let
--   $$(\partial_a f)(g)=\frac{d}{dt}\Big|_{t=0}f\big(g\,a(t)\big)$$
--   be its invariant differential operator, which maps $\mathcal S(G)$ into itself. For a character $\chi\in\widehat G$ the function $t\mapsto\chi(a(t))$ is a continuous character of $\mathbb R$, and the **symbol** (or polynomial) of $\partial_a$ is
--   $$p(\partial_a)(\chi)=(\partial_a\chi)(e)=\frac{d}{dt}\Big|_{t=0}\chi\big(a(t)\big)\in i\,\mathbb R .$$
--
--   **Statement.** For every $f\in\mathcal S(G)$ the function $\partial_a f$ is $\mu$-integrable and, for every $\chi\in\widehat G$,
--   $$\widehat{\partial_a f}(\chi)=p(\partial_a)(\chi)\cdot\widehat f(\chi).$$
--
--   For $G=\mathbb R$, $a(t)=t$ and $\chi_\xi(x)=e^{2\pi i\xi x}$ one has $p(\partial_a)(\chi_\xi)=2\pi i\xi$ and the formula is $\widehat{f'}(\xi)=2\pi i\xi\,\widehat f(\xi)$. Since the symbol is multiplicative, $p(\partial_{a_n}\cdots\partial_{a_1})=\prod_i p(\partial_{a_i})$ (Lemma D.1.6.13), iterating the statement and using linearity gives the general form $\mathcal F_G(Df)=p(D)\cdot\widehat f$ of (D.1.6.23) for every invariant differential operator $D\in\mathrm{Diff}(G)$. The source uses it to characterize rapid decay of $\widehat f$ (Lemma D.1.6.16) and to prove that $\mathcal F_G$ maps $\mathcal S(G)$ into $\mathcal S(\widehat G)$.
--
--   **Formalization Note.** $a$ is `a : Multiplicative ℝ →ₜ* G`; $\partial_a f$ is the function `fun g => deriv (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) 0` (the derivative exists by the companion statement `MasulloGRH.schwartzBruhat_oneParameterDeriv`), $p(\partial_a)(\chi)$ is `deriv (fun t : ℝ => (χ (a (Multiplicative.ofAdd t)) : ℂ)) 0`, and $\widehat{\ \cdot\ }$ is `RiemannMasullo.lcaFourier μ`. Integrability of $\partial_a f$ is part of the conclusion. The statement is for the generators $\partial_a$ of $\mathrm{Diff}(G)$; the algebra $\mathrm{Diff}(G)$ itself is not formalized. The Haar measure is assumed regular.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 773, Lemma D.1.6.19(1), eqs. (D.1.6.23)–(D.1.6.24), with Definition D.1.6.10 (p. 768); classical reference: A. Wawrzyńczyk, On tempered distributions and Bochner-Schwartz Theorem on arbitrary locally compact abelian groups, Colloquium Mathematicum XIX (1968), Theorem 3.2 (as cited in the source)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_RiemannMasullo_LCAFourierConvolution

open MeasureTheory Topology

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_fourier_oneParameterDeriv
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (a : Multiplicative ℝ →ₜ* G) (f : SchwartzBruhat G) (χ : PontryaginDual G) :
    Integrable (fun g : G => deriv (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) 0) μ ∧
    RiemannMasullo.lcaFourier μ
        (fun g : G => deriv (fun t : ℝ => f (g * a (Multiplicative.ofAdd t))) 0) χ =
      deriv (fun t : ℝ => ((χ (a (Multiplicative.ofAdd t)) : Circle) : ℂ)) 0 *
        RiemannMasullo.lcaFourier μ (f : G → ℂ) χ := by sorry

end MasulloGRH
