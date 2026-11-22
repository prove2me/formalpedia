-- Prove2me | Theorems.Thm_LCAGroup_isotypicSubspace_averaging_projection
-- name    : LCAGroup.isotypicSubspace_averaging_projection
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:33.347962+00:00
-- url     : https://prove2.me/theorems/397cce4b-5209-4aeb-8964-367a32594b05
-- title:
--   Isotypic projector $\mu(K)^{-1}\int_K\overline{\omega(k)}\pi(k)\,d\mu$ is the orthogonal projection onto $H(\omega)$; its kernel is the closed span of the $v-\overline{\omega(k)}\pi(k)v$
-- statement:
--   **Isotypic projectors of a unitary representation of a compact abelian group.** Averaging against the conjugate character is the orthogonal projection onto the isotypic subspace, and its kernel is the closed span of the "co-invariant" vectors.
--
--   Let $K$ be a compact Hausdorff abelian group with a Haar measure $\mu$ (so $0<\mu(K)<\infty$), let $H$ be a complex Hilbert space and let $\pi\colon K\to U(H)$ be a strongly continuous unitary representation. For a continuous character $\omega\in\widehat K$ let $H(\omega)=\{v:\pi(k)v=\omega(k)v\ \forall k\in K\}$ and define, for $v\in H$, the $H$-valued integral
--   $$P_\omega v=\frac{1}{\mu(K)}\int_K\overline{\omega(k)}\,\pi(k)v\,d\mu(k).$$
--   Then for every $v\in H$:
--
--   1. $P_\omega v\in H(\omega)$;
--   2. $v-P_\omega v\perp H(\omega)$;
--
--   so $P_\omega$ is the orthogonal projection of $H$ onto $H(\omega)$ (in particular it does not depend on the choice of Haar measure). Moreover
--
--   3. $$H(\omega)^\perp=\ker P_\omega=\overline{\operatorname{span}}\,\bigl\{\,v-\overline{\omega(k)}\,\pi(k)v\ :\ v\in H,\ k\in K\,\bigr\}.$$
--
--   This is the Hilbert-space case of Corollary 4.3.3.3 of the source (the operator $\Phi_{G,\omega}$ of (4.3.3.8), its range $\mathrm H^0(\omega,E)$, the idempotent $\mu_G(G)^{-1}\Phi_{G,\omega}$ and the description (3) of its kernel) and the statement of Corollary 4.3.3.4 that $\nu_1(G^1)^{-1}\Phi_{G^1,\omega}$ is an orthogonal projector; part 3 identifies the space whose quotient is the space of continuous $\omega$-co-invariants $\mathrm H_{0,\mathrm{cont}}(\omega,E)$ (Terminology 4.3.3.2).
--
--   **Formalization Note.** The integral is Mathlib's Bochner integral in $H$ (the integrand is continuous on the compact group $K$, hence integrable); $\mu(K)$ is `μ.real Set.univ`; complex conjugation is `starRingEnd ℂ`. The orthogonal projection is characterized by parts 1–2 (`∈ isotypicSubspace …` and `∈ (isotypicSubspace …)ᗮ`), which avoids a `HasOrthogonalProjection` instance. The closure in part 3 is `Submodule.topologicalClosure` of `Submodule.span ℂ {v - conj(ω k) • π k v}`. The source writes the normalization as $\nu_1(G^1)^{-1}$ for an arbitrary Haar measure $\nu_1$; the same factor appears here.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 183–185, Corollary 4.3.3.3(1)–(3), eq. (4.3.3.8), and Corollary 4.3.3.4; p. 180, Terminology 4.3.2.1; classical reference: A. Knapp, Representations of semisimple groups, Princeton University Press, Thm. 1.12 (consequence of the Peter–Weyl theorem, as cited by the paper); J. Conway, A First Course in Functional Analysis, Springer, Ch. II, §3, Prop. 3.3(f) (as cited by the paper)

import Mathlib
import Definitions.Def_LCAGroup_IsotypicSubspace

open MeasureTheory

set_option autoImplicit false

namespace LCAGroup

theorem isotypicSubspace_averaging_projection
    (K : Type*) [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : K →* (H →L[ℂ] H)) (hπ_unitary : ∀ k, π k ∈ unitary (H →L[ℂ] H))
    (hπ_cont : ∀ v : H, Continuous fun k => π k v) (ω : PontryaginDual K) :
    (∀ v : H, ((μ.real Set.univ)⁻¹ • ∫ k, (starRingEnd ℂ (ω k : ℂ)) • π k v ∂μ) ∈
        isotypicSubspace π fun k => (ω k : ℂ)) ∧
      (∀ v : H, (v - (μ.real Set.univ)⁻¹ • ∫ k, (starRingEnd ℂ (ω k : ℂ)) • π k v ∂μ) ∈
        (isotypicSubspace π fun k => (ω k : ℂ))ᗮ) ∧
      (isotypicSubspace π fun k => (ω k : ℂ))ᗮ =
        (Submodule.span ℂ
          {u : H | ∃ (v : H) (k : K), u = v - (starRingEnd ℂ (ω k : ℂ)) • π k v}).topologicalClosure := by
  sorry

end LCAGroup
