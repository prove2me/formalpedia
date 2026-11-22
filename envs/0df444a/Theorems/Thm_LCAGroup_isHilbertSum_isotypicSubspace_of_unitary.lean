-- Prove2me | Theorems.Thm_LCAGroup_isHilbertSum_isotypicSubspace_of_unitary
-- name    : LCAGroup.isHilbertSum_isotypicSubspace_of_unitary
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:29.125628+00:00
-- url     : https://prove2.me/theorems/9de365ff-d588-4fbd-bdff-7f9e08c9453f
-- title:
--   Peter–Weyl for compact abelian groups: a strongly continuous unitary representation is the Hilbert sum of its isotypic subspaces $H(\omega)$, $\omega\in\widehat K$
-- statement:
--   **Peter–Weyl decomposition for compact abelian groups.** Every strongly continuous unitary representation of a compact abelian group is the orthogonal Hilbert sum of its isotypic subspaces.
--
--   Let $K$ be a compact Hausdorff abelian group and let $\widehat K$ be its Pontryagin dual, the group of continuous characters $\omega\colon K\to U(1)$. Let $H$ be a complex Hilbert space and let $\pi\colon K\to U(H)$ be a homomorphism into the unitary operators of $H$ which is strongly continuous: $k\mapsto\pi(k)v$ is continuous for every $v\in H$. For $\omega\in\widehat K$ let
--   $$H(\omega)=\{v\in H:\ \pi(k)v=\omega(k)v\ \text{ for all } k\in K\}$$
--   be the $\omega$-isotypic subspace. Then:
--
--   1. the subspaces $H(\omega)$, $\omega\in\widehat K$, are pairwise orthogonal;
--   2. every $v\in H$ is the sum of an unconditionally convergent series $v=\sum_{\omega\in\widehat K}v_\omega$ with $v_\omega\in H(\omega)$ and $\sum_\omega\|v_\omega\|^2=\|v\|^2$; equivalently
--   $$H=\widehat{\bigoplus_{\omega\in\widehat K}}\,H(\omega)\qquad\text{(orthogonal Hilbert sum).}$$
--
--   This is the consequence of the Peter–Weyl theorem that the source invokes ([Kn, Thm. 1.12]) to decompose $R(G)=L^2(G,\nu)$ under the compact group $G^1$ of module-one elements (proof of Lemma 4.3.2.2, eq. (4.3.2.8), and proof of Corollary 4.3.3.4, density of the sum of the isotypes). Applied to the left regular representation it gives the decomposition of $L^2(G)$ into $K$-isotypes for a compact subgroup $K$ of a locally compact abelian group.
--
--   **Formalization Note.** The representation is `π : K →* (H →L[ℂ] H)` with `π k ∈ unitary (H →L[ℂ] H)` and strong continuity `∀ v, Continuous fun k => π k v`; characters are `PontryaginDual K`; $H(\omega)$ is `LCAGroup.isotypicSubspace π (fun k => (ω k : ℂ))`. The conclusion is Mathlib's `IsHilbertSum` for the inclusions of these closed subspaces: they form an orthogonal family and the induced isometry $\ell^2(\widehat K;H(\omega))\to H$, $(v_\omega)\mapsto\sum v_\omega$, is surjective. No second-countability or separability is assumed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 179, proof of Lemma 4.3.2.2, eq. (4.3.2.8); pp. 184–185, Corollary 4.3.3.4 and its proof; classical reference: A. Knapp, Representations of semisimple groups, Princeton University Press, Thm. 1.12 (consequence of the Peter–Weyl theorem, as cited by the paper)

import Mathlib
import Definitions.Def_LCAGroup_IsotypicSubspace

open MeasureTheory

set_option autoImplicit false

namespace LCAGroup

theorem isHilbertSum_isotypicSubspace_of_unitary
    (K : Type*) [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [T2Space K]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : K →* (H →L[ℂ] H)) (hπ_unitary : ∀ k, π k ∈ unitary (H →L[ℂ] H))
    (hπ_cont : ∀ v : H, Continuous fun k => π k v) :
    IsHilbertSum ℂ (fun ω : PontryaginDual K => ↥(isotypicSubspace π fun k => (ω k : ℂ)))
      (fun ω => (isotypicSubspace π fun k => (ω k : ℂ)).subtypeₗᵢ) := by
  sorry

end LCAGroup
