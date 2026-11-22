-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_poisson_summation
-- name    : MasulloGRH.schwartzBruhat_poisson_summation
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T15:23:16.270807+00:00
-- url     : https://prove2.me/theorems/75fe45df-e074-465a-ae2c-1c35bc57b6eb
-- title:
--   Theorem D.1.7.1(1) — Poisson summation for Schwartz–Bruhat functions: $\int_H f(yh)\,dh=\int_{H^\perp}\widehat f(\chi)\,\chi(y)\,d\chi$ for all $f\in\mathcal S(G)$, $y\in G$
-- statement:
--   **The Poisson summation formula on the Schwartz–Bruhat space** (Theorem D.1.7.1(1), eq. (D.1.7.3)).
--
--   Throughout, $G$ is a Hausdorff locally compact abelian group, written multiplicatively, and $\widehat G$ is its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$ with the compact-open topology). A closed subgroup $k\subseteq G$ is **good** if its annihilator $k^\perp=\{\chi\in\widehat G:\chi|_k=1\}$ is open and compactly generated in $\widehat G$ (then $k$ is compact). A pair $(\Gamma,k)$ of subgroups is **structural** if $\Gamma$ is open and compactly generated, $k$ is good and $k\subseteq\Gamma$; then $\Gamma/k$ is an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ ($F$ finite). $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ is the Fréchet space of functions on $G$ that vanish outside $\Gamma$, are $k$-invariant, and induce a smooth rapidly decreasing function on $\Gamma/k$. The **Schwartz–Bruhat space** is
--   $$\mathcal S(G)=\bigcup_{(\Gamma,k)}\mathcal S(k,\Gamma)$$
--   with the locally convex inductive limit topology (the finest locally convex topology making all inclusions $\mathcal S(k,\Gamma)\to\mathcal S(G)$ continuous).
--
--   Let $H\subseteq G$ be a closed subgroup. Fix Haar measures $\mu_G$ on $G$ and $\mu_H$ on $H$, and let $\mu_{G/H}$ be the Haar measure on $G/H$ determined by Weil's formula
--   $$\int_G\varphi\,d\mu_G=\int_{G/H}\Big(\int_H\varphi(xh)\,d\mu_H(h)\Big)\,d\mu_{G/H}(xH)\qquad(\varphi\in C_c(G)).$$
--   The dual group of $G/H$ is identified with the annihilator $H^\perp\subseteq\widehat G$ (a character $\eta$ of $G/H$ is the character $x\mapsto\eta(xH)$ of $G$ trivial on $H$), and $\mu_{H^\perp}$ denotes the Haar measure on $H^\perp=\widehat{G/H}$ dual to $\mu_{G/H}$ (the Plancherel measure). Let $\widehat f(\chi)=\int_G f(x)\overline{\chi(x)}\,d\mu_G(x)$.
--
--   **Statement.** For every $f\in\mathcal S(G)$ and every $y\in G$, the function $\chi\mapsto\widehat f(\chi)\chi(y)$ is $\mu_{H^\perp}$-integrable on $H^\perp$ and
--   $$\int_H f(yh)\,d\mu_H(h)=\int_{H^\perp}\widehat f(\chi)\,\chi(y)\,d\mu_{H^\perp}(\chi).$$
--
--   In contrast with the general Poisson formula for integrable functions, no hypothesis beyond $f\in\mathcal S(G)$ is needed and the identity holds at every point $y$. The left side is the value at $yH$ of the function $\Phi_H(f)\in\mathcal S(G/H)$ obtained by integrating $f$ over the cosets of $H$, and the right side is the Fourier inversion formula for it on $\widehat{G/H}=H^\perp$, where its Fourier transform is the restriction of $\widehat f$. For $G=\mathbb R$, $H=\mathbb Z$ it reads $\sum_{n}f(y+n)=\sum_{m}\widehat f(m)e^{2\pi imy}$, and for $G=\mathbb A_F$, $H=F$ it is the adelic Poisson formula behind the functional equation of theta functions and of Tate's zeta integrals. The source records it for use, in combination with its Theorems 4.6.2.1 and 4.6.1.5 and Lemma 4.4.2.6, in the construction of the absolute Schauder bases of its Theorem 7.3.1.6.
--
--   **Formalization Note.** The normalizations are those of the platform statement `LCAGroup.poisson_summation`: `ν` is a regular Haar measure on `G ⧸ H` satisfying Weil's formula for continuous compactly supported functions (hypothesis `hν`), `ν'` is a measure on `PontryaginDual (G ⧸ H)` with `LCAGroup.IsPlancherelMeasure ν ν'`, and the integral over $H^\perp$ is written as an integral over `η : PontryaginDual (G ⧸ H)` of `(∫ x, f x * star (η (x : G ⧸ H)) ∂μ) * η (y : G ⧸ H)`. The measures `μ`, `μH`, `ν` are regular Haar measures; such `ν` and `ν'` exist and are unique (Weil's formula and the Plancherel theorem).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 776–777, Theorem D.1.7.1(1), eq. (D.1.7.3)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_LCAGroup_PlancherelMeasure

open MeasureTheory Topology

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_poisson_summation
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    [MeasurableSpace (PontryaginDual (G ⧸ H))] [BorelSpace (PontryaginDual (G ⧸ H))]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure] [ν.Regular]
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ = ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂μH) ∂ν)
    (ν' : Measure (PontryaginDual (G ⧸ H))) (hν' : LCAGroup.IsPlancherelMeasure ν ν')
    (f : SchwartzBruhat G) (y : G) :
    Integrable (fun η : PontryaginDual (G ⧸ H) =>
        (∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) * (η (y : G ⧸ H) : ℂ)) ν' ∧
    ∫ h : H, f (y * (h : G)) ∂μH =
      ∫ η : PontryaginDual (G ⧸ H),
        (∫ x : G, f x * star (η (x : G ⧸ H) : ℂ) ∂μ) * (η (y : G ⧸ H) : ℂ) ∂ν' := by sorry

end MasulloGRH
