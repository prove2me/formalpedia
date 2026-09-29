-- Prove2me | Theorems.Thm_NumberField_exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain
-- name    : NumberField.exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/ad46ad59-f8ae-5a42-81ad-bbc85dfdbbe8
-- title:
--   Characters above ξ_L as integrals over norm fibres
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite and Galois, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$; equip the idele groups $(\mathbb{A}_L)^\times$ and $(\mathbb{A}_K)^\times$ with Borel measurable structures and Haar measures $\nu_{Z,L}$, $\nu_{Z,K}$. Let $\Theta \subseteq (\mathbb{A}_L)^\times$ be a fundamental domain for $\nu_{Z,L}$ for the image of the homomorphism $L^\times \to (\mathbb{A}_L)^\times$, $w \mapsto \sigma(w)/w$ followed by the embedding of principal ideles. Then there is a real $\kappa > 0$ such that the following holds for all data as follows: a homomorphism $\xi_L$ from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ whose associated $\mathbb{C}$-valued function is continuous and which is trivial on the principal ideles from $L^\times$; a finite set $\Xi$ of homomorphisms $\xi$ from the full subgroup of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, whose membership in $\Xi$ is equivalent to: continuity, triviality on the principal ideles from $K^\times$, and $\xi \circ N = \xi_L$, where $N$ is the idelic norm $(\mathbb{A}_L)^\times \to (\mathbb{A}_K)^\times$ obtained by applying the unit functor to the $\mathbb{A}_K$-algebra norm of $\mathbb{A}_L$, the algebra structure being that of the base change with its isomorphism $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$; a continuous compactly supported $F : (\mathbb{A}_K)^\times \to \mathbb{C}$; and a set $T \subseteq K^\times$ such that every $a \in K^\times$ admits exactly one $t \in T$ with $a = t \cdot \mathrm{N}_{L/K}(b)$ for some $b \in L^\times$. Writing $I(t) = \int_\Theta \xi_L(z)\,F(t \cdot N z)\,d\nu_{Z,L}(z)$, with $t$ embedded as a principal idele, the conclusion is threefold: the set of $t \in T$ with $I(t) \neq 0$ is finite; $\sum_{\xi \in \Xi} \int \xi(u) F(u)\,d\nu_{Z,K}(u) = (|\Xi|/\kappa) \sum^{\mathrm{f}}_{t \in T} I(t)$, the right-hand sum being a finsum over $T$; and if $\Xi = \emptyset$ then $I(t) = 0$ for every $t \in K^\times$.
--
--   This is the step, on the side of $K$, in the comparison of trace formulas for cyclic base change, that converts a sum over the idele class characters of $K$ lying above a given idele class character $\xi_L$ of $L$ into integrals along the fibres of the idelic norm over a fundamental domain $\Theta$, with the underlying class field theory (Hasse's norm theorem and Hilbert's Theorem 90 for the cyclic extension $L/K$) made explicit. It is used in the corresponding identity for integrals over the centre in the automorphic comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain.lean

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
        (_hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
        (_hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            ξL ⟨z, Subgroup.mem_top z⟩ = 1)
        (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
        (_hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
          ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
            (∀ z : (AdeleRing (𝓞 K) K)ˣ,
              z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
            ∀ z : (AdeleRing (𝓞 L) L)ˣ,
              ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
                ξL ⟨z, Subgroup.mem_top z⟩))
        (F : (AdeleRing (𝓞 K) K)ˣ → ℂ) (_hFc : Continuous F) (_hFs : HasCompactSupport F)
        (T : Set Kˣ)
        (_hT : ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b),
        (T ∩ Function.support fun t : Kˣ =>
            ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              F (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t *
                (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL).Finite ∧
        (∑ ξ ∈ Ξ, ∫ u : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨u, Subgroup.mem_top u⟩ : ℂˣ) : ℂ) * F u ∂νZK =
          ((Ξ.card : ℂ) / (κ : ℂ)) *
            ∑ᶠ t ∈ T, ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              F (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t *
                (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL) ∧
        (Ξ = ∅ → ∀ t : Kˣ,
          ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              F (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t *
                (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL = 0) := by sorry
