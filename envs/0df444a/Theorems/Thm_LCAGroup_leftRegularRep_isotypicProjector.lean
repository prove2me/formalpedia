-- Prove2me | Theorems.Thm_LCAGroup_leftRegularRep_isotypicProjector
-- name    : LCAGroup.leftRegularRep_isotypicProjector
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:32.185463+00:00
-- url     : https://prove2.me/theorems/dc9d2eaf-c5a8-417c-a693-18babbd1ee0b
-- title:
--   (4.3.2.1), Cor. 4.3.3.4 — the isotypic projector $P_\omega$ on $L^2(G)$ is the orthogonal projection onto $L^2(G)(\omega)$, commutes with translations, and $P_\psi P_\omega=0$ for $\psi\neq\omega$
-- statement:
--   **Isotypic projectors on $L^2(G)$** for a compact subgroup $K$ of a locally compact abelian group $G$ (eq. (4.3.2.1), Terminology 4.3.2.1 and Corollary 4.3.3.4 of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\nu$ (a Radon measure), let $\lambda(g)f(x)=f(g^{-1}x)$ be the left regular representation on $L^2(G,\nu)$, let $K\subseteq G$ be a compact subgroup with a Haar measure $\mu_K$, and for $\chi\in\widehat K$ let $L^2(G)(\chi)=\{f:\lambda(k)f=\chi(k)f\ \forall k\in K\}$. For $\chi\in\widehat K$ and $h\in L^2(G,\nu)$ define the $L^2(G,\nu)$-valued integral
--   $$P_\chi h=\frac{1}{\mu_K(K)}\int_K\overline{\chi(k)}\,\lambda(k)h\,d\mu_K(k).$$
--   Then for all $\omega,\psi\in\widehat K$, $f\in L^2(G,\nu)$ and $g\in G$:
--
--   1. $P_\omega f\in L^2(G)(\omega)$ and $f-P_\omega f\perp L^2(G)(\omega)$, i.e. $P_\omega$ is the orthogonal projection of $L^2(G,\nu)$ onto the $\omega$-isotype;
--   2. $P_\omega$ commutes with translations: $P_\omega(\lambda(g)f)=\lambda(g)(P_\omega f)$;
--   3. $P_\psi P_\omega f=0$ whenever $\psi\neq\omega$.
--
--   In the source $K=G^1$ and $P_\omega=\nu_1(G^1)^{-1}\Pi_{G^1,\omega}$, where $\Pi_{G,\omega}(\phi)(x)=\int_{G^1}\overline{\omega(g)}\,\phi(g^{-1}x)\,d\nu_1(g)$ is (4.3.2.1); Terminology 4.3.2.1 calls it the projection onto the $\omega$-isotype, and Corollary 4.3.3.4 shows that these operators are orthogonal projectors with mutually orthogonal ranges. They are used throughout Chapter 4 to pass between $L^2(G)$, or $\mathcal S(G)$, and its $G^1$-isotypes.
--
--   **Formalization Note.** $P_\chi$ is introduced by a `let` and uses Mathlib's Bochner integral in the Hilbert space `Lp ℂ 2 ν`, i.e. the vector-valued form $\Phi_{G^1,\omega}$ of the operator, which the source identifies with the pointwise formula (4.3.2.1) (Corollary 4.3.3.4, eq. (4.3.3.10); Remark 4.3.3.2). The normalization $\mu_K(K)^{-1}$ (`μK.real Set.univ`) is the source's $\nu_1(G^1)^{-1}$. `[ν.IsHaarMeasure] [ν.Regular]` is a Haar measure in the classical Radon sense (automatic for second-countable $G$); $\mu_K$ is any Haar measure on $K$. $\lambda$ is `LCAGroup.leftRegularRep ν 2` and the isotypes are `LCAGroup.isotypicSubspace`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 178, eq. (4.3.2.1); p. 180, Terminology 4.3.2.1; pp. 184–185, Corollary 4.3.3.4, eq. (4.3.3.10); classical reference: A. Knapp, Representations of semisimple groups, Princeton University Press, Thm. 1.12 (consequence of the Peter–Weyl theorem, as cited by the paper); J. Conway, A First Course in Functional Analysis, Springer, Ch. II, §3, Prop. 3.3(f) (as cited by the paper)

import Mathlib
import Definitions.Def_LCAGroup_IsotypicSubspace
import Definitions.Def_LCAGroup_LeftRegularRep

open MeasureTheory

set_option autoImplicit false

namespace LCAGroup

theorem leftRegularRep_isotypicProjector
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] [ν.Regular]
    (K : Subgroup G) [CompactSpace K] (μK : Measure K) [μK.IsHaarMeasure]
    (ω : PontryaginDual K) (f : Lp ℂ 2 ν) :
    let P : PontryaginDual K → Lp ℂ 2 ν → Lp ℂ 2 ν := fun χ h =>
      (μK.real Set.univ)⁻¹ • ∫ k, (starRingEnd ℂ (χ k : ℂ)) • leftRegularRep ν 2 (k : G) h ∂μK
    P ω f ∈ isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G)) (fun k => (ω k : ℂ)) ∧
      f - P ω f ∈
        (isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G)) fun k => (ω k : ℂ))ᗮ ∧
      (∀ g : G, P ω (leftRegularRep ν 2 g f) = leftRegularRep ν 2 g (P ω f)) ∧
      (∀ ψ : PontryaginDual K, ψ ≠ ω → P ψ (P ω f) = 0) := by
  sorry

end LCAGroup
