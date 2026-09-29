-- Prove2me | Theorems.Thm_NumberField_setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one
-- name    : NumberField.setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/c441c264-4f64-5942-859b-98a779d4faa8
-- title:
--   Vanishing of a character integral against functions of the idelic norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$, and let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$. Fix Borel measurable structures on the idele groups $(\mathbb{A}_L)^\times$ and $(\mathbb{A}_K)^\times$ and a Haar measure $\nu_{Z,L}$ on $(\mathbb{A}_L)^\times$. Let $N$ denote the idelic norm $(\mathbb{A}_L)^\times\to(\mathbb{A}_K)^\times$ attached to [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87), i.e. the map induced on units by the algebra norm of $\mathbb{A}_L$ over $\mathbb{A}_K$ for the algebra structure given by the ring homomorphism $\mathbb{A}_K\to\mathbb{A}_L$ of that base-change datum (which is compatible with $K\to L$ on principal adeles and carries an isomorphism $\mathbb{A}_K\otimes_K L\cong\mathbb{A}_L$ sending $1\otimes l$ to $l$). Let $\Theta\subseteq(\mathbb{A}_L)^\times$ be a fundamental domain, for $\nu_{Z,L}$, for the translation action of the image of the homomorphism $L^\times\to(\mathbb{A}_L)^\times$, $w\mapsto \sigma(w)/w$ viewed as a principal idele. Let $\xi$ be a homomorphism from $(\mathbb{A}_L)^\times$ (as the top subgroup) to $\mathbb{C}^\times$ such that $z\mapsto\xi(z)$ is continuous as a complex-valued function, $\xi$ is trivial on the principal ideles $L^\times$, and there exists $t$ with $N t=1$ and $\xi(t)\neq1$. Then for every measurable $g:(\mathbb{A}_K)^\times\to\mathbb{C}$, $\int_{\Theta}\xi(z)\,g(Nz)\,d\nu_{Z,L}(z)=0$.
--
--   This is the vanishing alternative in the adelic computation of a Herbrand-type quotient: an idele class character of $L$ that is non-trivial somewhere on the norm-one ideles contributes nothing to the integral of $\xi\cdot(g\circ N)$ over a fundamental domain for the ideles $\sigma(w)/w$, $w\in L^\times$. It is used by [`NumberField.exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain`](thm.html#NumberField.exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain) and [`NumberField.sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_setIntegral_comp_idelicNorm_eq_mul`](thm.html#NumberField.sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_setIntegral_comp_idelicNorm_eq_mul), where the remaining characters are those trivial on the norm-one ideles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one.lean

import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (hker : ∃ t : (AdeleRing (𝓞 L) L)ˣ,
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm t = 1 ∧ ξ ⟨t, Subgroup.mem_top t⟩ ≠ 1)
    (g : (AdeleRing (𝓞 K) K)ˣ → ℂ) (hg : Measurable g) :
    ∫ z in Θ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL = 0 := by sorry
