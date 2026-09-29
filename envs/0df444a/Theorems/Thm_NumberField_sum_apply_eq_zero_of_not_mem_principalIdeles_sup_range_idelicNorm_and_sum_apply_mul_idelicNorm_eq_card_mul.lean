-- Prove2me | Theorems.Thm_NumberField_sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul
-- name    : NumberField.sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/8a2412b7-cbe9-5aa4-bc54-61b3ee4370d9
-- title:
--   Orthogonality of idele class characters above ξ_L
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$, and write $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K` and $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`. Let $\xi_L$ be an arbitrary monoid homomorphism from the full subgroup $\top$ of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$ (no continuity or invariance is assumed of it). Let $\Xi$ be a finite set of monoid homomorphisms $\top \le \mathbb{A}_K^\times \to \mathbb{C}^\times$, assumed to consist of exactly those $\xi$ such that: the complex-valued function $z \mapsto \xi(z)$ is continuous on $\mathbb{A}_K^\times$; $\xi(z) = 1$ for every $z$ in the range of the map on units induced by $\mathrm{algebraMap}\, K\, \mathbb{A}_K$; and $\xi(N z) = \xi_L(z)$ for all $z \in \mathbb{A}_L^\times$, where $N =$ `idelicNorm` of `genuineBaseChange K L`, i.e. the map on unit groups induced by the algebra norm of $\mathbb{A}_L$ over $\mathbb{A}_K$ taken along the ring homomorphism `genuineβ K L`. The conclusion is twofold: first, $\sum_{\xi \in \Xi} \xi(z) = 0$ for every $z \in \mathbb{A}_K^\times$ lying outside the join of `principalIdeles (𝓞 K) K` (the range of the units map induced by $\mathrm{algebraMap}\,K\,\mathbb{A}_K$) with the range of $N$; second, for all $k \in K^\times$ and $w \in \mathbb{A}_L^\times$, $\sum_{\xi \in \Xi} \xi(k \cdot N w) = |\Xi| \, \xi_L(w)$, all sums being of the underlying complex numbers.
--
--   This is the orthogonality relation for the set of continuous idele class characters of $K$ whose composite with the idelic norm is a prescribed character $\xi_L$: such characters form a coset of the dual of the quotient $\mathbb{A}_K^\times/(K^\times \cdot N\mathbb{A}_L^\times)$, and their sum detects membership in $K^\times \cdot N\mathbb{A}_L^\times$. Openness of the norm subgroup enters via [`NumberField.isOpen_range_idelicNorm`](thm.html#NumberField.isOpen_range_idelicNorm), and the result is used in the automorphic-form estimate comparing character-folded window integrals with Satake data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul.lean

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩)) :
    (∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∉ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) →
        ∑ ξ ∈ Ξ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = 0) ∧
    (∀ (k : Kˣ) (w : (AdeleRing (𝓞 L) L)ˣ),
      ∑ ξ ∈ Ξ, ((ξ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k *
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
        (Ξ.card : ℂ) * ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ)) := by sorry
