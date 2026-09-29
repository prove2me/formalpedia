-- Prove2me | Theorems.Thm_NumberField_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_setIntegral_comp_idelicNorm_eq_mul
-- name    : NumberField.sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_setIntegral_comp_idelicNorm_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/46ddc341-ccee-5393-a037-deb4fd0bd4bb
-- title:
--   Sum of base-change characters against a test function, given κ
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite Galois, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every automorphism lies in the subgroup of integer powers of $\sigma$. Fix Borel-measurable structures and Haar measures $\nu_{Z,L}$ on $(\mathbb{A}_L)^\times$ and $\nu_{Z,K}$ on $(\mathbb{A}_K)^\times$, and let $\Theta \subseteq (\mathbb{A}_L)^\times$ be a fundamental domain for $\nu_{Z,L}$ under the range of the homomorphism $L^\times \to (\mathbb{A}_L)^\times$, $w \mapsto \sigma(w)w^{-1}$ followed by the inclusion of principal ideles. Write $N$ for the idelic norm attached to `genuineBaseChange K L`, namely the unit map of the algebra norm of $\mathbb{A}_L$ over $\mathbb{A}_K$ along the base-change ring homomorphism with $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$. Let $\kappa > 0$ satisfy the fibre-integration identity $\int_\Theta g(Nz)\,d\nu_{Z,L} = \kappa \int_{\mathrm{range}\,N} g(u)\,d\nu_{Z,K}$ for every measurable $g : (\mathbb{A}_K)^\times \to \mathbb{C}$. Let $\xi_L$ be a homomorphism from the top subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function and trivial on principal ideles, and let $\Xi$ be a finite set of homomorphisms on the top subgroup of $(\mathbb{A}_K)^\times$ whose members are exactly those $\xi$ that are continuous, trivial on principal ideles of $K$, and satisfy $\xi \circ N = \xi_L$. Let $F : (\mathbb{A}_K)^\times \to \mathbb{C}$ be continuous with compact support, and let $T \subseteq K^\times$ be such that every $a \in K^\times$ has a unique $t \in T$ with $a = t\,\mathrm{N}_{L/K}(b)$ for some $b \in L^\times$. Put $I(t) = \int_\Theta \xi_L(z)\,F(t \cdot Nz)\,d\nu_{Z,L}(z)$, with $t$ viewed as a principal idele. Then (i) $T$ meets the support of $I$ in a finite set; (ii) $\sum_{\xi \in \Xi} \int_{(\mathbb{A}_K)^\times} \xi(u)F(u)\,d\nu_{Z,K}(u) = (|\Xi|/\kappa)\sum_{t \in T}^{\mathrm{f}} I(t)$, the right-hand sum being a finsum over $T$; and (iii) if $\Xi = \varnothing$ then $I(t) = 0$ for every $t \in K^\times$.
--
--   This is the form of the cyclic base-change character identity in which the fibre-integration constant $\kappa$ is supplied as a hypothesis rather than produced, so that consumers carrying their own constant can use it directly; the characters in $\Xi$ are the translates of one of them by the characters of the finite group $(\mathbb{A}_K)^\times / K^\times N((\mathbb{A}_L)^\times)$. It is used in the per-class comparison of trace formulas for cyclic base change, where the central and norm-twisted orbital contributions are matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_setIntegral_comp_idelicNorm_eq_mul.lean

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_setIntegral_comp_idelicNorm_eq_mul
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
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (κ : ℝ) (hκ : 0 < κ)
    (hκi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        κ * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (F : (AdeleRing (𝓞 K) K)ˣ → ℂ) (hFc : Continuous F) (hFs : HasCompactSupport F)
    (T : Set Kˣ)
    (hT : ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b) :
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
