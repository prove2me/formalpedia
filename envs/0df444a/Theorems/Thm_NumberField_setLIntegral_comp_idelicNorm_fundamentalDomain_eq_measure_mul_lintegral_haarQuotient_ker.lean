-- Prove2me | Theorems.Thm_NumberField_setLIntegral_comp_idelicNorm_fundamentalDomain_eq_measure_mul_lintegral_haarQuotient_ker
-- name    : NumberField.setLIntegral_comp_idelicNorm_fundamentalDomain_eq_measure_mul_lintegral_haarQuotient_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/12848420-24e5-5841-bee4-8b9254751f7e
-- title:
--   From a Γ-fundamental domain to the norm-one idele quotient
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite-dimensional $K$-algebra, and let $\sigma$ be a $K$-automorphism of $L$. Write $N$ for the idelic norm $(\mathbb{A}_L)^\times \to (\mathbb{A}_K)^\times$ attached to the base change [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87), namely the map induced on units by the algebra norm of $\mathbb{A}_L$ over $\mathbb{A}_K$ along the ring homomorphism $\beta$ of that base change. Both idele groups carry a measurable structure which is the Borel structure of their topology, and $\nu_{Z,L}$ is a Haar measure on $(\mathbb{A}_L)^\times$. Let $N_1$ be a closed subgroup of $(\mathbb{A}_L)^\times$ whose members are exactly the $z$ with $N(z)=1$, equipped with a Haar measure $\mu_N$, and let $\Gamma$ denote the range of the homomorphism $L^\times \to (\mathbb{A}_L)^\times$ sending $w$ to the idele attached to $\sigma(w)w^{-1}$. Assume $\Theta \subseteq (\mathbb{A}_L)^\times$ is a fundamental domain for $\Gamma$ with respect to $\nu_{Z,L}$, and $\Theta_1 \subseteq N_1$ is a fundamental domain, with respect to $\mu_N$, for $\Gamma$ regarded as a subgroup of $N_1$. Let $\bar\nu$ be the quotient measure [`HaarQuotient.measure`](def/HaarQuotient.html#L28) $\nu_{Z,L}\,N_1\,\mu_N$ on the orbit quotient of $(\mathbb{A}_L)^\times$ by $N_1$, i.e. the image under the quotient map of $\nu_{Z,L}$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25)$\,N_1\,\mu_N$. Then two assertions hold. First, for every measurable $g : (\mathbb{A}_K)^\times \to [0,\infty]$, $$\int_{\Theta} g(N z)\,d\nu_{Z,L} = \mu_N(\Theta_1)\int g\bigl(N(\mathrm{out}(wq))\bigr)\,d\bar\nu(wq),$$ the integrand on the right being evaluated at a chosen representative $\mathrm{out}(wq)$ of each orbit. Second, if $\mu_N(\Theta_1) < \infty$ then for every measurable $g : (\mathbb{A}_K)^\times \to \mathbb{C}$ the function $z \mapsto g(Nz)$ is integrable on $\Theta$ for $\nu_{Z,L}$ if and only if $\mu_N(\Theta_1)=0$ or $wq \mapsto g(N(\mathrm{out}(wq)))$ is integrable for $\bar\nu$, and the corresponding identity of Bochner integrals holds with the real number $\mu_N(\Theta_1)$ as factor.
--
--   This is the "quotient in stages" step for the tower $\Gamma \backslash (\mathbb{A}_L)^\times \to N_1 \backslash (\mathbb{A}_L)^\times$: integration of a function of the idelic norm over a fundamental domain for the principal norm-one ideles $\sigma(w)/w$ is replaced by integration over the quotient by the full norm-one subgroup, at the cost of the factor $\mu_N(\Theta_1)$, in both the $[0,\infty]$-valued and the complex-valued form. It is used in the computation [`AutomorphicForm.setIntegral_twistedEllipticCentralFold_eq_const_mul_sum_of_factorization_of_normFibre`](thm.html#AutomorphicForm.setIntegral_twistedEllipticCentralFold_eq_const_mul_sum_of_factorization_of_normFibre), where an integral over a fundamental domain is rewritten along the fibres of the norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_setLIntegral_comp_idelicNorm_fundamentalDomain_eq_measure_mul_lintegral_haarQuotient_ker.lean

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.setLIntegral_comp_idelicNorm_fundamentalDomain_eq_measure_mul_lintegral_haarQuotient_ker
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (Θ₁ : Set N1)
    (hΘ₁ : IsFundamentalDomain
      ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) Θ₁ μN) :
    (∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        μN Θ₁ *
          ∫⁻ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN)) ∧
    (μN Θ₁ < ∞ →
      ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
        (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
          (μN Θ₁ = 0 ∨
            Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
              g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)))
              (HaarQuotient.measure νZL N1 μN))) ∧
        ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
          (μN Θ₁).toReal *
            ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
              g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
              ∂(HaarQuotient.measure νZL N1 μN)) := by sorry
