-- Prove2me | Theorems.Thm_NumberField_exists_isCompact_ker_idelicNorm_subset_range_mul_of_forall_mem_zpowers
-- name    : NumberField.exists_isCompact_ker_idelicNorm_subset_range_mul_of_forall_mem_zpowers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/313a5765-d0c8-52f5-af35-974746ea05e3
-- title:
--   Compactness of norm-one ideles modulo σ(w)/w
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, i.e. $\sigma$ generates the (hence cyclic) Galois group. Write $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K` and $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, and let $N$ be the idelic norm $\mathbb{A}_L^\times \to \mathbb{A}_K^\times$ of the base change `genuineBaseChange K L`: that is, $N$ is obtained by applying `Units.map` to the algebra norm of $\mathbb{A}_L$ over $\mathbb{A}_K$, taken for the algebra structure coming from the ring homomorphism `genuineβ K L` $\colon \mathbb{A}_K \to \mathbb{A}_L$ which is compatible with the embeddings of $K$ and $L$ and which identifies $\mathbb{A}_K \otimes_K L$ with $\mathbb{A}_L$ as $\mathbb{A}_K$-algebras. The assertion is that there is a compact set $D \subseteq \mathbb{A}_L^\times$ such that, as sets of ideles, $\ker N$ is contained in the pointwise product $\Gamma \cdot D$, where $\Gamma$ is the range of the homomorphism $L^\times \to \mathbb{A}_L^\times$ sending $w$ to the principal idele attached to $\sigma(w)w^{-1}$ (the quotient of `Units.map` of $\sigma$ by the identity of $L^\times$, followed by `Units.map` of the embedding $L \to \mathbb{A}_L$).
--
--   This is the compactness, modulo rational points, of the adelic points of the norm-one torus $T = \ker(N \colon R_{L/K}\mathbb{G}_m \to \mathbb{G}_m)$ for cyclic $L/K$, the rational points being the elements $\sigma(w)/w$ by Hilbert's Theorem 90, stated here in the form of a covering of $\ker N$ by finitely many translates' worth of a single compact set. It is used in the computation of integrals of functions pulled back along the idelic norm, in [`NumberField.exists_setLIntegral_comp_idelicNorm_eq_mul_and_setIntegral_comp_idelicNorm_eq_mul`](thm.html#NumberField.exists_setLIntegral_comp_idelicNorm_eq_mul_and_setIntegral_comp_idelicNorm_eq_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isCompact_ker_idelicNorm_subset_range_mul_of_forall_mem_zpowers.lean

import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped Pointwise

theorem NumberField.exists_isCompact_ker_idelicNorm_subset_range_mul_of_forall_mem_zpowers
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    ∃ D : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact D ∧
      ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.ker :
          Set (AdeleRing (𝓞 L) L)ˣ) ⊆
        (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
            (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range :
          Set (AdeleRing (𝓞 L) L)ˣ) * D := by sorry
