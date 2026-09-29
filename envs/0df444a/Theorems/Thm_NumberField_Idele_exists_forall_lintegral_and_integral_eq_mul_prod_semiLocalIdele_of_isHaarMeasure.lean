-- Prove2me | Theorems.Thm_NumberField_Idele_exists_forall_lintegral_and_integral_eq_mul_prod_semiLocalIdele_of_isHaarMeasure
-- name    : NumberField.Idele.exists_forall_lintegral_and_integral_eq_mul_prod_semiLocalIdele_of_isHaarMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/7a8cd862-fc22-5293-ac84-2bdaf45e9992
-- title:
--   Factorisation of Haar measure on the ideles of L over places of K
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, let the unit group $(\mathbb{A}_L)^\times$ of the adele ring of $L$ carry a measurable space structure that is the Borel one for its topology, and let $\nu$ be a Haar measure on $(\mathbb{A}_L)^\times$. The assertion is that there exist a constant $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$, a measure $\nu_a$ on $(\mathbb{A}_{L,\infty})^\times$ for the Borel $\sigma$-algebra of the infinite adele ring units, and measures $\nu_v$ on $(L \otimes_K K_v)^\times$ for each height-one prime $v$ of $\mathcal{O}_K$, such that $\nu_a$ is a Haar measure, each $\nu_v$ is a Haar measure giving mass $1$ to `integralUnits K L v`, the subgroup of units of the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_v \to L \otimes_K K_v$, and two factorisation identities hold. Write $t_\infty$ for the image of $t$ under `Units.map` applied to the first projection $\mathbb{A}_{L,\infty} \times \mathbb{A}_{L,f} \to \mathbb{A}_{L,\infty}$, and $t_v$ for `semiLocalIdele K L v t`, obtained from the finite part of $t$ by the ring map sending a finite adele to its components at the places $w \mid v$ of $L$, read in $L \otimes_K K_v$ through the base-change isomorphism. First, for every finite set $S$ of primes of $\mathcal{O}_K$, every Borel measurable $g \colon (\mathbb{A}_{L,\infty})^\times \to [0,\infty]$ and every family $f_v \colon (L \otimes_K K_v)^\times \to [0,\infty]$ measurable for $v \in S$, the lower Lebesgue integral over $(\mathbb{A}_L)^\times$ of $g(t_\infty) \prod_{v \in S} f_v(t_v)$ times the indicator of $\{t \mid t_v \in \mathrm{integralUnits}(v) \text{ for all } v \notin S\}$ equals $c \bigl(\int g \, d\nu_a\bigr) \prod_{v \in S} \int f_v \, d\nu_v$. Second, for $\mathbb{C}$-valued $g$ integrable for $\nu_a$ and $f_v$ integrable for $\nu_v$ ($v \in S$), the corresponding integrand is $\nu$-integrable and its Bochner integral equals $c$, read as a real number and then in $\mathbb{C}$, times $\bigl(\int g \, d\nu_a\bigr) \prod_{v \in S} \int f_v \, d\nu_v$.
--
--   This is the restricted-product factorisation of Haar measure on the idele group of $L$, with the finite places of $L$ grouped according to the place of $K$ they lie over, in the two forms needed in practice: for $[0,\infty]$-valued measurable functions and for complex-valued integrable ones. It extends the $[0,\infty]$-valued statement [`NumberField.Idele.exists_forall_lintegral_eq_mul_lintegral_mul_prod_lintegral_semiLocalIdele_of_isHaarMeasure`](thm.html#NumberField.Idele.exists_forall_lintegral_eq_mul_lintegral_mul_prod_lintegral_semiLocalIdele_of_isHaarMeasure) by the Bochner-integral clause, and is used in the computation of twisted orbital integrals over a transversal, where the unramified local factors are separated from the finitely many places carrying data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_forall_lintegral_and_integral_eq_mul_prod_semiLocalIdele_of_isHaarMeasure.lean

import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel

theorem NumberField.Idele.exists_forall_lintegral_and_integral_eq_mul_prod_semiLocalIdele_of_isHaarMeasure
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (ν : Measure (AdeleRing (𝓞 L) L)ˣ)
    [ν.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    ∃ (νa : @Measure (InfiniteAdeleRing L)ˣ (borel (InfiniteAdeleRing L)ˣ))
      (νf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ),
      @Measure.IsHaarMeasure (InfiniteAdeleRing L)ˣ _ _ (borel (InfiniteAdeleRing L)ˣ) νa ∧
      (∀ v, (νf v).IsHaarMeasure ∧
        νf v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : (InfiniteAdeleRing L)ˣ → ℝ≥0∞)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞),
        @Measurable _ _ (borel (InfiniteAdeleRing L)ˣ) _ g →
        (∀ v ∈ S, Measurable (f v)) →
        ∫⁻ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
            (∏ v ∈ S, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂ν =
          c * (∫⁻ x, g x ∂νa) * ∏ v ∈ S, ∫⁻ x, f v x ∂(νf v)) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : (InfiniteAdeleRing L)ˣ → ℂ)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℂ),
        Integrable g νa →
        (∀ v ∈ S, Integrable (f v) (νf v)) →
        Integrable (fun t : (AdeleRing (𝓞 L) L)ˣ =>
            g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
              (∏ v ∈ S, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
              Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
                  AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                    AutomorphicForm.TransversalMeasure.integralUnits K L v}
                (fun _ => (1 : ℂ)) t) ν ∧
        ∫ t, g (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) *
            (∏ v ∈ S, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℂ)) t ∂ν =
          ((c.toReal : ℝ) : ℂ) * (∫ x, g x ∂νa) * ∏ v ∈ S, ∫ x, f v x ∂(νf v) := by sorry
