-- Prove2me | Theorems.Thm_NumberField_setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one
-- name    : NumberField.setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/46c43348-71a9-5662-bd6b-45e53eab61ec
-- title:
--   Vanishing of int_Ω ξ F when ξ(t)≠ 1
-- statement:
--   Let $K$ be a number field and let $\mathbb{I}_K = (\mathbb{A}_K)^\times$ denote the unit group of its adele ring, equipped with a measurable space structure which is the Borel structure of its topology, and let $\nu_{Z,K}$ be a Haar measure on $\mathbb{I}_K$. Write $\Gamma$ for the range of the map $\mathbb{I}_K \supseteq$ induced on units by the structure map $K \to \mathbb{A}_K$, i.e. the subgroup of principal ideles. Assume given a set $\Omega_K \subseteq \mathbb{I}_K$ which is a fundamental domain for the action of $\Gamma$ on $\mathbb{I}_K$ with respect to $\nu_{Z,K}$; a group homomorphism $\xi_K$ from the full subgroup $\top \le \mathbb{I}_K$ to $\mathbb{C}^\times$ (no continuity is required) which takes the value $1$ at every principal idele; an element $t \in \mathbb{I}_K$ with $\xi_K(t) \neq 1$; and a function $F : \mathbb{I}_K \to \mathbb{C}$ satisfying $F(\gamma z) = F(z)$ for all $\gamma \in \Gamma$ and all $z$, and $F(zt) = F(z)$ for all $z$ (no measurability or integrability of $F$ is assumed). Then the Bochner integral of $z \mapsto \xi_K(z) F(z)$ over $\Omega_K$ against $\nu_{Z,K}$ is $0$.
--
--   This is the orthogonality relation expressing that the integral over a fundamental domain for $K^\times \subset \mathbb{I}_K$ of a $K^\times$-invariant function against an idele class character dies as soon as the character is non-trivial on a direction along which the function is invariant. It is used to show that central folds of automorphic forms against a central character vanish, in the three variants for the central elliptic part, the hyperbolic cell and the twisted hyperbolic cell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξKt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (t : (AdeleRing (𝓞 K) K)ˣ) (ht : ξK ⟨t, Subgroup.mem_top t⟩ ≠ 1)
    (F : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hFK : ∀ γ : (AdeleRing (𝓞 K) K)ˣ,
      γ ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ∀ z : (AdeleRing (𝓞 K) K)ˣ, F (γ * z) = F z)
    (hFt : ∀ z : (AdeleRing (𝓞 K) K)ˣ, F (z * t) = F z) :
    ∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * F z ∂νZK = 0 := by sorry
