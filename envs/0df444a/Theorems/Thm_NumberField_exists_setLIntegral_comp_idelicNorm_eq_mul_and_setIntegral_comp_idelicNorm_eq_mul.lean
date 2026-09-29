-- Prove2me | Theorems.Thm_NumberField_exists_setLIntegral_comp_idelicNorm_eq_mul_and_setIntegral_comp_idelicNorm_eq_mul
-- name    : NumberField.exists_setLIntegral_comp_idelicNorm_eq_mul_and_setIntegral_comp_idelicNorm_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/558f42f9-a448-53bf-803d-b5128e0c3904
-- title:
--   Fibre integration of the idelic norm over a fundamental domain
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, finite-dimensional and Galois over $K$, and suppose $\sigma \in \mathrm{Gal}(L/K)$ is such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Equip the idele groups $(\mathbb{A}_L)^\times$ and $(\mathbb{A}_K)^\times$ (units of `AdeleRing (𝓞 L) L` and `AdeleRing (𝓞 K) K`) with measurable structures that are the Borel structures of their topologies, and let $\nu_L$, $\nu_K$ be Haar measures on them. Let $N$ denote the map on units induced by the algebra norm of $\mathbb{A}_L$ over $\mathbb{A}_K$ attached to the base change `genuineBaseChange K L`, that is to the ring map $\mathbb{A}_K \to \mathbb{A}_L$ compatible with $K \to L$ together with the isomorphism $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$. Let $\Theta \subseteq (\mathbb{A}_L)^\times$ be a fundamental domain, in the sense of `IsFundamentalDomain` for $\nu_L$, for the subgroup which is the image of the homomorphism $L^\times \to (\mathbb{A}_L)^\times$, $w \mapsto \sigma(w)/w$, composed with the inclusion of principal ideles. Then there exists a real $\kappa > 0$ such that: for every measurable $g : (\mathbb{A}_K)^\times \to [0,\infty]$ one has $\int^-_{\Theta} g(Nz)\,d\nu_L = \mathrm{ofReal}(\kappa)\cdot \int^-_{\mathrm{range}\,N} g\,d\nu_K$; and for every measurable $g : (\mathbb{A}_K)^\times \to \mathbb{C}$, the function $z \mapsto g(Nz)$ is integrable on $\Theta$ for $\nu_L$ if and only if $g$ is integrable on $\mathrm{range}\,N$ for $\nu_K$, and $\int_{\Theta} g(Nz)\,d\nu_L = \kappa \int_{\mathrm{range}\,N} g\,d\nu_K$.
--
--   This is the integration-along-fibres step for the idelic norm of a cyclic extension of number fields: integrals over a fundamental domain for the principal ideles $\sigma(w)/w$ of a function pulled back along $N$ are computed as a fixed positive multiple of integrals over the norm subgroup. It is used in the comparison of integrals and sums occurring in the base-change arguments, being cited by the matching statement for sums of integrals over a fundamental domain and by the statement comparing sums over centraliser domains for matching automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_setLIntegral_comp_idelicNorm_eq_mul_and_setIntegral_comp_idelicNorm_eq_mul.lean

import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal

theorem NumberField.exists_setLIntegral_comp_idelicNorm_eq_mul_and_setIntegral_comp_idelicNorm_eq_mul
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
      (∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
        ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
          ENNReal.ofReal κ *
            ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK) ∧
      ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
        (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
          IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
        ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
          κ * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK := by sorry
