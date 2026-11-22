-- Prove2me | Theorems.Thm_MasulloGRH_elemSchwartz_fourier_of_equiv_elemGroup
-- name    : MasulloGRH.elemSchwartz_fourier_of_equiv_elemGroup
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T19:55:48.158847+00:00
-- url     : https://prove2.me/theorems/96511434-45b2-4cf5-9c9e-84f44c89a222
-- title:
--   Fourier transform on an elementary group $A\cong\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$: $\mathcal S(E)\to\mathcal S(\widehat A)$ continuously (auxiliary for Lemma D.1.6.19(2))
-- statement:
--   **Fourier transform on an elementary group** (auxiliary lemma for Lemma D.1.6.19(2)): for a locally compact abelian group $A$ isomorphic to an elementary group $E$, the Fourier transform maps the Schwartz–Bruhat space $\mathcal S(E)$, transported to $A$, continuously into the Schwartz–Bruhat space of an elementary group isomorphic to $\widehat A$.
--
--   Let $A$ be a Hausdorff locally compact abelian group, written multiplicatively, with its Borel $\sigma$-algebra and a Haar measure $\nu$, and let $\widehat A$ be its Pontryagin dual (continuous characters $\chi\colon A\to U(1)$, compact-open topology). Let
--   $$E=\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times\textstyle\prod_{i<s}\mathbb Z/d_i\qquad(\mathbb T=\mathbb R/\mathbb Z,\ \text{all } d_i\neq0)$$
--   be an elementary abelian Lie group and $\varphi\colon A\to E$ an isomorphism of topological groups. Let $\mathcal S(E)$ be the elementary Schwartz–Bruhat space of Definition D.1.3.1: the functions $g$ on $E$ that are smooth in $(x,z)\in\mathbb R^m\times\mathbb T^n$ and such that $|a|^j\,|x|^i\,\|D^k_{(x,z)}g(x,z,a,b)\|$ is bounded for all $i,j,k$, with the locally convex topology of these seminorms.
--
--   **Statement.** There are an elementary group
--   $$E'=\mathbb R^{m'}\times\mathbb T^{n'}\times\mathbb Z^{r'}\times\textstyle\prod_{i<s'}\mathbb Z/d'_i\qquad(\text{all } d'_i\neq0),$$
--   an isomorphism of topological groups $\varphi'\colon\widehat A\to E'$, and a continuous linear map $T\colon\mathcal S(E)\to\mathcal S(E')$ such that for every $g\in\mathcal S(E)$:
--   1. $g\circ\varphi$ is $\nu$-integrable;
--   2. for every $\chi\in\widehat A$,
--   $$\int_A g(\varphi(x))\,\overline{\chi(x)}\,d\nu(x)=(Tg)(\varphi'(\chi)).$$
--
--   Classically one takes $E'=\mathbb R^m\times\mathbb T^r\times\mathbb Z^n\times\prod_i\mathbb Z/d_i$, identified with $\widehat E$ through the pairing $\langle(\xi,\theta,\ell,c),(x,z,a,b)\rangle=\exp\bigl(2\pi i(\xi\cdot x+\ell\cdot z+\theta\cdot a+\sum_i c_ib_i/d_i)\bigr)$, and $\varphi'$ the composite of $\chi\mapsto\chi\circ\varphi^{-1}$ with this identification; then $T$ is, up to the positive constant comparing $\varphi_*\nu$ with the standard Haar measure of $E$, the Fourier transform of $E$: the Fourier transform of Schwartz functions on $\mathbb R^m$, Fourier coefficients on $\mathbb T^n$ (smooth functions to rapidly decreasing sequences on $\mathbb Z^n$), Fourier series on $\mathbb Z^r$ (rapidly decreasing sequences to smooth functions on $\mathbb T^r$), and the discrete Fourier transform on the finite factor. This is the analytic input of Lemma D.1.6.19(2): for a structural pair $(\Gamma,k)$ of a locally compact abelian group $G$ and a presentation $\Gamma/k\cong E$, the Fourier transform of the stage $\mathcal S(k,\Gamma)$ of $\mathcal S(G)$ is computed on $\Gamma/k\cong E$, and the stage is carried into the stage $\mathcal S(\Gamma^\perp,k^\perp)$ of $\mathcal S(\widehat G)$ through $k^\perp/\Gamma^\perp\cong\widehat{\Gamma/k}$.
--
--   **Formalization Note.** The elementary groups are `ElemGroup m n r s d` and the spaces $\mathcal S(E)$ are `ElemSchwartz m n r s d` with their seminorm topology (platform definition `MasulloGRH_SchwartzBruhat`); since groups are written multiplicatively, $E$ enters as `Multiplicative (ElemGroup m n r s d)` and $\varphi$ as a `ContinuousMulEquiv`. The Fourier transform is `RiemannMasullo.lcaFourier ν f χ = ∫ x, f x * star (χ x) ∂ν` (platform definition `RiemannMasullo_LCAFourierConvolution`); assertion 2 is an equality of functions on $\widehat A$ (for every $\chi$, not almost everywhere). No regularity of $\nu$ is assumed ($A\cong E$ is second countable, so every Haar measure on $A$ is regular). The hypothesis $d_i\neq0$ is needed: `ZMod 0` is $\mathbb Z$, on which $\mathcal S(E)$ imposes no decay. Only "into, continuously" is asserted (not that $T$ is an isomorphism).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 773, Lemma D.1.6.19(2) (the Fourier transform of the elementary group Γ/k, used for the stages of S(G)); auxiliary lemma for the proof of Lemma D.1.6.19(2) (via MasulloGRH.schwartzBruhat_stage_fourier); classical reference: F. Bruhat, Distributions sur un groupe localement compact et applications à l'étude des représentations des groupes p-adiques, Bull. Soc. Math. France 89 (1961); M. S. Osborne, On the Schwartz–Bruhat space and the Paley–Wiener theorem for locally compact abelian groups, J. Funct. Anal. 19 (1975), 40–49

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_RiemannMasullo_LCAFourierConvolution

open MeasureTheory Topology

set_option autoImplicit false

namespace MasulloGRH

theorem elemSchwartz_fourier_of_equiv_elemGroup
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (ν : Measure A) [ν.IsHaarMeasure]
    (m n r s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, d i ≠ 0)
    (φ : A ≃ₜ* Multiplicative (ElemGroup m n r s d)) :
    ∃ (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (φ' : PontryaginDual A ≃ₜ* Multiplicative (ElemGroup m' n' r' s' d'))
      (T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d'),
      (∀ i, d' i ≠ 0) ∧ Continuous T ∧
      ∀ g : ElemSchwartz m n r s d,
        Integrable (fun x : A => g.toFun (Multiplicative.toAdd (φ x))) ν ∧
          RiemannMasullo.lcaFourier ν (fun x : A => g.toFun (Multiplicative.toAdd (φ x))) =
            fun χ : PontryaginDual A => (T g).toFun (Multiplicative.toAdd (φ' χ)) := by sorry

end MasulloGRH
