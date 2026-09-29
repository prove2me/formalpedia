-- Prove2me | Theorems.Thm_NumberField_measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm
-- name    : NumberField.measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/f84dc809-66e0-54c2-888d-1673aec70f03
-- title:
--   Covolume of the principal norm-one ideles in a cyclic extension
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite and Galois, let $D$ be an idele Galois descent datum for $L/K$ (a monoid homomorphism from $L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of $\mathbb{A}_L$, compatible with the embedding of $L$ and continuous), and let $\sigma$ be an automorphism such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Fix Haar measures $\nu_{Z,L}$ on $\mathbb{A}_L^\times$ and $\nu_{Z,K}$ on $\mathbb{A}_K^\times$ (for the Borel structures), with sets $\Omega_L$, $\Omega_K$ that are fundamental domains for the ranges of $L^\times \to \mathbb{A}_L^\times$, resp. $K^\times \to \mathbb{A}_K^\times$. Let $A_K \le \mathbb{A}_L^\times$ be a closed subgroup whose elements are exactly the images of units of $\mathbb{A}_K$ under the ring homomorphism $\beta$ of the base-change datum `genuineBaseChange`, equipped with a Haar measure $\mu_{A_K}$ such that integration of any $\mathbb{C}$-valued $g$ over $A_K$ agrees with integration of $g \circ \beta$ over $\mathbb{A}_K^\times$ against $\nu_{Z,K}$. Let $N^1 \le \mathbb{A}_L^\times$ be a closed subgroup whose elements are exactly the ideles of norm $1$, the norm being `Units.map` applied to the algebra norm of $\mathbb{A}_L$ over $\mathbb{A}_K$ along $\beta$, with a Haar measure $\mu_N$, and let $c_N > 0$ be such that for every $g$ the integral of $g$ over $N^1$ against $\mu_N$ equals $c_N$ times the integral over the orbit space of $A_K$ acting on $\mathbb{A}_L^\times$, against [`HaarQuotient.measure`](def/HaarQuotient.html#L28) $\nu_{Z,L}\,A_K\,\mu_{A_K}$, of $q \mapsto g(\sigma(q_{\mathrm{out}})\, q_{\mathrm{out}}^{-1})$, where $\sigma$ acts through the units automorphism induced by $D$. Finally let $\Theta_1 \subseteq N^1$ be a fundamental domain, for $\mu_N$, of the subgroup of $N^1$ induced by the range of $w \mapsto \sigma(w)/w$ on $L^\times$ composed with the embedding of $L^\times$ into $\mathbb{A}_L^\times$. Then $\mu_N(\Theta_1)$ is the extended-nonnegative-real number attached to $c_N \cdot [L:K] \cdot V_L / V_K$, where $V_L$ and $V_K$ are the real measures of $\Omega_L \cap \{z : \|z\|_L \in [1,e]\}$ and $\Omega_K \cap \{a : \|a\|_K \in [1,e]\}$, the idele norm being the value of the distributive Haar character.
--
--   This is the covolume computation for the principal norm-one ideles $\{\sigma(w)/w : w \in L^\times\}$ inside the group $N^1$ of norm-one ideles of a cyclic extension, in the measure normalisation ($A_K$, $\mu_{A_K}$, $N^1$, $\mu_N$, $c_N$) used for unfolding integrals over the centre. It is used in the evaluation of the twisted elliptic central fold as a constant times a sum over the relevant norm fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm.lean

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_SigmaAdelicAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)

    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νZK)

    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))

    (Θ₁ : Set N1)
    (hΘ₁ : IsFundamentalDomain
      ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) Θ₁ μN) :
    μN Θ₁ = ENNReal.ofReal (cN * (Module.finrank K L : ℝ) *
      (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal /
      (νZK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal) := by sorry
