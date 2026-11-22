-- Prove2me | Theorems.Thm_LCAGroup_leftRegularRep_isHilbertSum_isotypicSubspace
-- name    : LCAGroup.leftRegularRep_isHilbertSum_isotypicSubspace
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:30.379969+00:00
-- url     : https://prove2.me/theorems/10144bfe-cac9-478f-bb26-210c63248918
-- title:
--   Lemma 4.3.2.2, normalization-free form — $L^2(G)$, $G$ locally compact abelian, is the Hilbert sum of the non-zero isotypes $L^2(G)(\omega)$, $\omega\in\widehat K$, of a compact subgroup $K$
-- statement:
--   **Isotypic decomposition of $L^2(G)$ under a compact subgroup** (Lemma 4.3.2.2 of the source, normalization-free form).
--
--   Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\nu$ (a Radon measure), let $K\subseteq G$ be a compact subgroup, and let $\lambda(g)f(x)=f(g^{-1}x)$ be the left regular representation of $G$ on $L^2(G,\nu)$. For a continuous character $\omega\in\widehat K$ let
--   $$L^2(G)(\omega)=\{f\in L^2(G,\nu):\ \lambda(k)f=\omega(k)f\ \text{ for all }k\in K\}$$
--   be the $\omega$-isotype. Then:
--
--   1. $L^2(G,\nu)$ is the orthogonal Hilbert sum of the isotypes,
--   $$L^2(G,\nu)=\widehat{\bigoplus_{\omega\in\widehat K}}\,L^2(G)(\omega);$$
--   2. every isotype is non-zero: $L^2(G)(\omega)\neq0$ for all $\omega\in\widehat K$.
--
--   In the source, $G$ is a second-countable $\mathbf R_{>0}$-modulated group (e.g. the idele class group $C_F$ or $J_{F,S}$) and $K=G^1$ is the compact subgroup of module-one elements; the proof of Lemma 4.3.2.2 establishes $L^2(G,\nu)\simeq\widehat\bigoplus_{i\in I}H_i$ (4.3.2.8) with $H_i=H_{\omega_i}$ the isotypes and $I=\widehat{G^1}$. The isotypes $R(G)(\omega)$ (Terminology 4.3.2.1) are the spaces on which the periodic Schauder bases of Chapter 4 are built.
--
--   **Deviation from the source.** The printed Lemma 4.3.2.2 asserts that the operator $\Pi_\tau=(\Pi_\omega)_{\omega\in\widehat{G^1}}\colon L^2(G,\nu)\to\widehat\bigoplus_{\omega\in\widehat{G^1}}L^2_\omega(\mathbf R_{>0},dt/t)$ is a surjective isometry. There $\nu_1$ is the chosen Haar measure on $G^1$, $\tau\colon\mathbf R_{>0}\to G$ is a continuous homomorphic section of the module $|\cdot|_G$, $L^2_\omega(\mathbf R_{>0},dt/t)$ is the Hilbert space $L^2(\mathbf R_{>0},dt/t)$ on which $G^1$ acts through the character $\omega$ ((4.3.2.2)–(4.3.2.3)), and the $\omega$-component $\Pi_\omega=\Pi_{G,\omega,\tau}$ of $\Pi_\tau$ is given on $\phi\in C_c(G)$ by $\Pi_\omega\phi(t)=\int_{G^1}\overline{\omega(g)}\,\phi(g^{-1}\tau(t))\,d\nu_1(g)$ and extended by continuity ((4.3.2.1)–(4.3.2.7)). Whether $\Pi_\tau$ is isometric depends on how the Haar measures are normalized: if $c>0$ is the constant with $\nu_1\otimes\tau_*(dt/t)=c\,\nu$ (via $G^1\times\mathbf R_{>0}\cong G$, $(g,t)\mapsto g\,\tau(t)$), one only has $\sum_\omega\|\Pi_\omega f\|^2=\nu_1(G^1)\,c\,\|f\|^2$ in general. This normalization issue is also recorded as erratum I73 of the independent mccorvie/riemann-masullo formalization (https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md). We state the normalization-free classical content proved in the source: the Hilbert-sum decomposition into isotypes and the non-vanishing of every isotype. We state it for an arbitrary compact subgroup $K$ of an arbitrary Hausdorff locally compact abelian group; the source's case is $K=G^1$.
--
--   **Formalization Note.** `[ν.IsHaarMeasure] [ν.Regular]` is a Haar measure in the classical (Radon) sense of the cited references; regularity is automatic when $G$ is second countable, the source's standing assumption. $K$ is a `Subgroup G` with `[CompactSpace K]`, $\widehat K$ is `PontryaginDual K`, $\lambda$ is `LCAGroup.leftRegularRep ν 2` and the isotypes are `LCAGroup.isotypicSubspace`. Part 1 is Mathlib's `IsHilbertSum` (orthogonal family whose induced isometry from the $\ell^2$-sum is surjective); part 2 is `≠ ⊥`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 179–180, Lemma 4.3.2.2 and its proof, eq. (4.3.2.8); p. 180, Terminology 4.3.2.1; classical reference: A. Knapp, Representations of semisimple groups, Princeton University Press, Thm. 1.12 (consequence of the Peter–Weyl theorem, as cited by the paper)

import Mathlib
import Definitions.Def_LCAGroup_IsotypicSubspace
import Definitions.Def_LCAGroup_LeftRegularRep

open MeasureTheory

set_option autoImplicit false

namespace LCAGroup

theorem leftRegularRep_isHilbertSum_isotypicSubspace
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] [ν.Regular]
    (K : Subgroup G) [CompactSpace K] :
    IsHilbertSum ℂ
        (fun ω : PontryaginDual K =>
          ↥(isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G)) fun k => (ω k : ℂ)))
        (fun ω =>
          (isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G))
            fun k => (ω k : ℂ)).subtypeₗᵢ) ∧
      ∀ ω : PontryaginDual K,
        isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G)) (fun k => (ω k : ℂ)) ≠ ⊥ := by
  sorry

end LCAGroup
