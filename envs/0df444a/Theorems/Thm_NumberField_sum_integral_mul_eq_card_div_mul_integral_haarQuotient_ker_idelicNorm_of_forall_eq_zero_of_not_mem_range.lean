-- Prove2me | Theorems.Thm_NumberField_sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range
-- name    : NumberField.sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/0806a5f7-7ef2-5333-a8e4-1fbfa09a53fc
-- title:
--   Summing int ξ F over characters above ξ_L via the norm fibration
-- statement:
--   Let $K \subseteq L$ be number fields, and equip the idele unit groups $(\mathbb{A}_K)^\times$ and $(\mathbb{A}_L)^\times$ (units of `AdeleRing (𝓞 K) K`, `AdeleRing (𝓞 L) L`) with measurable and Borel structures and Haar measures $\nu_{ZK}$, $\nu_{ZL}$. Write $\mathrm{Nrm}$ for the idelic norm of the base change `genuineBaseChange K L`, i.e. the map induced on units by the algebra norm of `AdeleRing (𝓞 L) L` over `AdeleRing (𝓞 K) K` along the base-change ring homomorphism. Let $N^1 \le (\mathbb{A}_L)^\times$ be a closed subgroup whose elements are exactly the $z$ with $\mathrm{Nrm}(z) = 1$, carrying a Haar measure $\mu_N$, and let [`HaarQuotient.measure νZL N1 μN`](def/HaarQuotient.html#L28) be the measure on the orbit quotient `MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ` obtained by pushing forward $\nu_{ZL}$ weighted by the density [`HaarQuotient.density N1 μN`](def/HaarQuotient.html#L25). Assume $C > 0$ is a constant such that, for every measurable $g$ on $(\mathbb{A}_K)^\times$, integration of $g \circ \mathrm{Nrm}$ (evaluated at chosen representatives `wq.out`) over the quotient equals $C$ times the integral of $g$ over the set $\mathrm{range}\,\mathrm{Nrm}$ with respect to $\nu_{ZK}$: in the lower Lebesgue integral form for $\mathbb{R}_{\ge 0}^\infty$-valued $g$, and in the Bochner form together with the equivalence of integrability of $g \circ \mathrm{Nrm}$ on the quotient with integrability of $g$ on $\mathrm{range}\,\mathrm{Nrm}$ for $\mathbb{C}$-valued $g$. Let $\xi_L$ be a monoid homomorphism from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ whose associated $\mathbb{C}$-valued function is continuous, and let $\Xi$ be a finite set of monoid homomorphisms $\xi$ from the full subgroup of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ whose members are characterised as those $\xi$ that are continuous as $\mathbb{C}$-valued functions, trivial on the image of $K^\times$ under the map on units induced by $K \to \mathbb{A}_K$, and satisfy $\xi(\mathrm{Nrm}(z)) = \xi_L(z)$ for all $z \in (\mathbb{A}_L)^\times$. Finally let $F : (\mathbb{A}_K)^\times \to \mathbb{C}$ be measurable, with $\xi \cdot F$ integrable against $\nu_{ZK}$ for each $\xi \in \Xi$, and with $F(z) = 0$ whenever $z \notin \mathrm{range}\,\mathrm{Nrm}$. The conclusion is twofold: if $\Xi$ is non-empty then $wq \mapsto \xi_L(wq.\mathrm{out}) \, F(\mathrm{Nrm}(wq.\mathrm{out}))$ is integrable for [`HaarQuotient.measure νZL N1 μN`](def/HaarQuotient.html#L28); and $$\sum_{\xi \in \Xi} \int_{(\mathbb{A}_K)^\times} \xi(z) F(z) \, d\nu_{ZK} = \frac{|\Xi|}{C} \int \xi_L(wq.\mathrm{out}) \, F(\mathrm{Nrm}(wq.\mathrm{out})) \, d(\mathrm{HaarQuotient.measure}\ \nu_{ZL}\ N1\ \mu_N).$$
--
--   This is the comparison of idelic integrals used in the hyperbolic-term matching for cyclic base change: the characters of $K$ lying above a fixed character $\xi_L$ of $L$ all agree on the group of idelic norms, so the $|\Xi|$ integrals coincide and the norm-fibration constant $C$ transfers the common value to the quotient $(\mathbb{A}_L)^\times/N^1$. It feeds the two slope-comparison statements [`AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm`](thm.html#AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm) and [`AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add`](thm.html#AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range.lean

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]

    (C : ℝ) (hC : 0 < C)
    (hCl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ENNReal, Measurable g →
        ∫⁻ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          ENNReal.ofReal C *
            ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hCi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
        (Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)))
            (HaarQuotient.measure νZL N1 μN) ↔
          IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          C * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)

    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))

    (F : (AdeleRing (𝓞 K) K)ˣ → ℂ) (hFm : Measurable F)
    (hFi : ∀ ξ ∈ Ξ, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * F z) νZK)
    (hF0 : ∀ z : (AdeleRing (𝓞 K) K)ˣ, z ∉ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm → F z = 0) :
    (Ξ.Nonempty → Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
          F ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)))
      (HaarQuotient.measure νZL N1 μN)) ∧
    ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * F z ∂νZK =
      ((Ξ.card : ℂ) / (C : ℂ)) *
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            F ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)) ∂(HaarQuotient.measure νZL N1 μN) := by sorry
