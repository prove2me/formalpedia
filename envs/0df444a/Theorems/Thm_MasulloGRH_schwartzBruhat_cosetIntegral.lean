-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_cosetIntegral
-- name    : MasulloGRH.schwartzBruhat_cosetIntegral
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T15:23:03.543109+00:00
-- url     : https://prove2.me/theorems/d81f831e-b59d-4af8-ba31-18ffee008c45
-- title:
--   Theorem D.1.7.1(2) — integration over the cosets of a closed subgroup $H$ is a continuous linear surjection $\Phi_H\colon\mathcal S(G)\to\mathcal S(G/H)$
-- statement:
--   **Push-forward of Schwartz–Bruhat functions to a quotient group** (Theorem D.1.7.1, the mapping property and part (2) without countability).
--
--   Throughout, $G$ is a Hausdorff locally compact abelian group, written multiplicatively, and $\widehat G$ is its Pontryagin dual (continuous characters $\chi\colon G\to U(1)$ with the compact-open topology). A closed subgroup $k\subseteq G$ is **good** if its annihilator $k^\perp=\{\chi\in\widehat G:\chi|_k=1\}$ is open and compactly generated in $\widehat G$ (then $k$ is compact). A pair $(\Gamma,k)$ of subgroups is **structural** if $\Gamma$ is open and compactly generated, $k$ is good and $k\subseteq\Gamma$; then $\Gamma/k$ is an elementary abelian Lie group $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ ($F$ finite). $\mathcal S(k,\Gamma)\cong\mathcal S(\Gamma/k)$ is the Fréchet space of functions on $G$ that vanish outside $\Gamma$, are $k$-invariant, and induce a smooth rapidly decreasing function on $\Gamma/k$. The **Schwartz–Bruhat space** is
--   $$\mathcal S(G)=\bigcup_{(\Gamma,k)}\mathcal S(k,\Gamma)$$
--   with the locally convex inductive limit topology (the finest locally convex topology making all inclusions $\mathcal S(k,\Gamma)\to\mathcal S(G)$ continuous).
--
--   Let $H\subseteq G$ be a closed subgroup with a Haar measure $\mu_H$. The quotient $G/H$ is again a Hausdorff locally compact abelian group, with its own Schwartz–Bruhat space $\mathcal S(G/H)$.
--
--   **Statement.** For every $f\in\mathcal S(G)$ and every $x\in G$ the function $h\mapsto f(xh)$ is $\mu_H$-integrable on $H$, the function
--   $$\Phi_H(f)(xH)=\int_H f(xh)\,d\mu_H(h)$$
--   on $G/H$ belongs to $\mathcal S(G/H)$, and the resulting map
--   $$\Phi_H\colon\mathcal S(G)\longrightarrow\mathcal S(G/H)$$
--   is linear, continuous and **surjective**.
--
--   For $H=\mathbb Z^n\subseteq G=\mathbb R^n$ this is the periodization map $\mathcal S(\mathbb R^n)\to C^\infty(\mathbb T^n)$, $f\mapsto\sum_{\ell\in\mathbb Z^n}f(\cdot+\ell)$; for $G=\mathbb A_F$ and $H=F$ it is the summation over the rational points that produces theta functions on $\mathbb A_F/F$. Under the Fourier transform $\Phi_H$ corresponds to restriction of functions from $\widehat G$ to the closed subgroup $H^\perp\cong\widehat{G/H}$. The source uses the theorem, in combination with its Theorems 4.6.2.1 and 4.6.1.5 and Lemma 4.4.2.6, to construct the absolute Schauder bases of its Theorem 7.3.1.6.
--
--   **Formalization Note.** `SchwartzBruhat (G ⧸ H)` is the platform Schwartz–Bruhat space of the quotient topological group. The statement asserts the existence of a continuous linear map `Φ : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ H)` that is surjective and satisfies, for all `f` and `x`, integrability of `fun h : H => f (x * h)` with respect to `μH` and `Φ f (x : G ⧸ H) = ∫ h : H, f (x * h) ∂μH`. `H` carries the Borel σ-algebra induced from `G`, and `μH` is a regular Haar measure on it. The companion statement `MasulloGRH.schwartzBruhat_cosetIntegral_isOpenQuotientMap` adds openness for second countable `G`, and `MasulloGRH.schwartzBruhat_poisson_summation` is formula (D.1.7.3).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 776–777, Theorem D.1.7.1 (mapping property and part (2)), eqs. (D.1.7.1)–(D.1.7.2)

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat

open MeasureTheory Topology

set_option autoImplicit false

namespace MasulloGRH

theorem schwartzBruhat_cosetIntegral
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular] :
    ∃ Φ : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ H),
      Function.Surjective Φ ∧
      ∀ (f : SchwartzBruhat G) (x : G),
        Integrable (fun h : H => f (x * (h : G))) μH ∧
        Φ f (x : G ⧸ H) = ∫ h : H, f (x * (h : G)) ∂μH := by sorry

end MasulloGRH
