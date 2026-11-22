-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_fourier_equiv
-- name    : MasulloGRH.schwartzBruhat_fourier_equiv
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T15:23:05.229829+00:00
-- url     : https://prove2.me/theorems/ac4067f2-3da9-4a81-b0d2-680a776e5b42
-- title:
--   Lemma D.1.6.19(2) — the Fourier transform is a linear topological isomorphism $\mathcal S(G)\xrightarrow{\ \sim\ }\mathcal S(\widehat G)$
-- statement:
--   **The Fourier transform on the Schwartz–Bruhat space** (Lemma D.1.6.19(2)).
--
--   Throughout, $G$ is a Hausdorff locally compact abelian group, written multiplicatively, and $\widehat G$ is its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$ with the compact-open topology). A closed subgroup $k\subseteq G$ is **good** if its annihilator $k^\perp=\{\chi\in\widehat G:\chi|_k=1\}$ is open and compactly generated in $\widehat G$ (then $k$ is compact). A pair $(\Gamma,k)$ of subgroups is **structural** if $\Gamma$ is open and compactly generated, $k$ is good and $k\subseteq\Gamma$; then $\Gamma/k$ is an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ ($F$ finite). $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ is the Fréchet space of functions on $G$ that vanish outside $\Gamma$, are $k$-invariant, and induce a smooth rapidly decreasing function on $\Gamma/k$. The **Schwartz–Bruhat space** is
--   $$\mathcal S(G)=\bigcup_{(\Gamma,k)}\mathcal S(k,\Gamma)$$
--   with the locally convex inductive limit topology (the finest locally convex topology making all inclusions $\mathcal S(k,\Gamma)\to\mathcal S(G)$ continuous).
--
--   Fix a Haar measure $\mu$ on $G$. Every $f\in\mathcal S(G)$ is $\mu$-integrable, and its Fourier transform is the function on $\widehat G$
--   $$\widehat f(\chi)=\mathcal F_G(f)(\chi)=\int_G f(x)\,\overline{\chi(x)}\,d\mu(x).$$
--
--   **Statement.** For every $f\in\mathcal S(G)$ the function $\widehat f$ belongs to the Schwartz–Bruhat space $\mathcal S(\widehat G)$ of the dual group, and
--   $$\mathcal F_G\colon\mathcal S(G)\longrightarrow\mathcal S(\widehat G),\qquad f\longmapsto\widehat f,$$
--   is a linear topological isomorphism: it is linear, bijective, continuous, and its inverse is continuous, for the locally convex inductive limit topologies of $\mathcal S(G)$ and $\mathcal S(\widehat G)$.
--
--   No countability assumption on $G$ is made. On the stages the theorem says that $\mathcal F_G$ maps $\mathcal S(k,\Gamma)$ onto $\mathcal S(\Gamma^\perp,k^\perp)$ and is there (up to a positive constant) the Fourier transform $\mathcal S(\Gamma/k)\to\mathcal S(\widehat{\Gamma/k})$ of the elementary abelian Lie group $\Gamma/k$; for $G=\mathbb R^n$ it is the classical statement that the Fourier transform is an automorphism of the Schwartz space, and for $G=\mathbb T^n$ that $C^\infty(\mathbb T^n)$ corresponds to the rapidly decreasing sequences on $\mathbb Z^n$. It is the basic tool of the source's harmonic analysis on Schwartz–Bruhat spaces, for instance in the proof of the distributional Poisson summation formula (Theorem D.1.7.1).
--
--   **Formalization Note.** `SchwartzBruhat G` is the platform definition `MasulloGRH_SchwartzBruhat` (a type of functions `G → ℂ` with its topology), used for `G` and for `PontryaginDual G`. The statement asserts the existence of a continuous linear equivalence `F : SchwartzBruhat G ≃L[ℂ] SchwartzBruhat (PontryaginDual G)` such that every `f` is `μ`-integrable and `F f χ = RiemannMasullo.lcaFourier μ f χ = ∫ x, f x * star (χ x) ∂μ` for all `χ`. The Haar measure is assumed regular (automatic for second countable `G`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 773, Lemma D.1.6.19(2)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_RiemannMasullo_LCAFourierConvolution

open MeasureTheory Topology

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_fourier_equiv
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ F : SchwartzBruhat G ≃L[ℂ] SchwartzBruhat (PontryaginDual G),
      ∀ f : SchwartzBruhat G, Integrable (f : G → ℂ) μ ∧
        ∀ χ : PontryaginDual G, F f χ = RiemannMasullo.lcaFourier μ (f : G → ℂ) χ := by sorry

end MasulloGRH
