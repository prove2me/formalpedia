-- Prove2me | Theorems.Thm_OAI_Problem310_AdaptiveLabels_measure_adaptive_failures
-- name    : OAI.Problem310.AdaptiveLabels.measure_adaptive_failures
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:08:54.650935+00:00
-- url     : https://prove2.me/theorems/afa8414e-0e82-4eb6-add0-3732c8584761
-- title:
--   Failure probability of adaptively addressed Boolean tests on an independent label table
-- statement:
--   Let $(A,\mathcal{A})$ be a measurable space with an arbitrary measure $\mu$ (for instance the law of a selector outcome $a$), let $I$ and $K$ be finite sets, and let $\nu$ be a probability measure on the Boolean set $\{\mathsf{false},\mathsf{true}\}$, which carries the discrete $\sigma$-algebra. A random table $\omega\in\{\mathsf{false},\mathsf{true}\}^K$ has the product law $\nu^{\otimes K}$ (independent entries with law $\nu$), and the pair $(a,\omega)$ is distributed according to the product measure $\mu\otimes\nu^{\otimes K}$ on $A\times\{\mathsf{false},\mathsf{true}\}^K$. Let $\mathrm{addr}:A\times I\to K$ be such that for every $a\in A$ the map $i\mapsto\mathrm{addr}(a,i)$ is injective, let $\mathrm{active}(a,i)$ be a decidable predicate on $A\times I$, and put
--   $$N(a)=\#\{i\in I:\ \mathrm{active}(a,i)\}.$$
--   Consider the event that every active test fails,
--   $$F=\bigl\{(a,\omega):\ \omega_{\mathrm{addr}(a,i)}=\mathsf{false}\ \text{for every } i\in I\ \text{with}\ \mathrm{active}(a,i)\bigr\},$$
--   and assume that $F$ is measurable for the product $\sigma$-algebra. Then
--
--   $$(\mu\otimes\nu^{\otimes K})(F)=\int_A\nu(\{\mathsf{false}\})^{N(a)}\,d\mu(a).$$
--
--   The addresses and the set of active tests may depend in an arbitrary way on the selector outcome $a$, which is independent of the table. Once $a$ is fixed, the active tests read pairwise distinct entries of the table, so the conditional probability that they all fail is $\nu(\{\mathsf{false}\})$ raised to the number of active tests. This turns failure probabilities of adaptively routed tests into an average of explicit geometric factors over the selector.
--
--   **Formalization Note** No finiteness assumption is made on $\mu$: Mathlib's `μ.prod` is defined for arbitrary measures, and its section formula holds because the second factor `Measure.pi (fun _ : K => ν)` is a probability measure. The right-hand side is the lower Lebesgue integral `∫⁻` of an extended-nonnegative-real valued function, which needs no measurability of the integrand; measurability of $F$ is the hypothesis `hmeas`. The count $N(a)$ is `(Finset.univ.filter (active a)).card`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/AdaptiveLabels.lean#L54-L83

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic

open OAI OAI.Problem310
universe u_I u_K u_B u_A
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem OAI.Problem310.AdaptiveLabels.measure_adaptive_failures
    {A : Type u_A} {I : Type u_I} {K : Type u_K} [MeasurableSpace A] [Fintype I] [Fintype K]
    (μ : Measure A) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → I → K) (hinj : ∀ a, Function.Injective (addr a))
    (active : A → I → Prop) [∀ a i, Decidable (active a i)]
    (hmeas : MeasurableSet {z : A × (K → Bool) |
      ∀ i, active z.1 i → z.2 (addr z.1 i) = false}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → Bool) | ∀ i, active z.1 i → z.2 (addr z.1 i) = false} =
      ∫⁻ a, (ν {false}) ^ (Finset.univ.filter (active a)).card ∂μ := by sorry
