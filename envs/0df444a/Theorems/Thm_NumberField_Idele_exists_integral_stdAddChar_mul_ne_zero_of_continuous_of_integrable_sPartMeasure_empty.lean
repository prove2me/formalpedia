-- Prove2me | Theorems.Thm_NumberField_Idele_exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty
-- name    : NumberField.Idele.exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/b649ca77-0ea6-5010-964c-1169754f5bb3
-- title:
--   An archimedean twist makes a non-trivial idele integral non-zero
-- statement:
--   Let $K$ be a number field, and give the idele group $(\mathbb{A}_K)^{\times} = (\mathtt{AdeleRing }(\mathcal{O}_K)\,K)^{\times}$ its Borel $\sigma$-algebra. Write $\nu$ for the measure [`NumberField.Idele.sPartMeasure K ∅`](def/NumberField_IdeleProductMeasure.html#L458), that is, the pushforward along the unit-group homomorphism `partAt K ∅` (induced by `partAtAdele K ∅`) of a Haar measure of the idele group restricted to the subgroup `unitIdelesOutside (𝓞 K) K ∅` of those unit ideles $\delta$ whose finite component at every finite place $v$ lies in the valuation ring $\mathcal{O}_v$ and whose inverse has the same property, i.e. whose finite part is an integral unit idele everywhere. Let $h : (\mathbb{A}_K)^{\times} \to \mathbb{C}$ be continuous and $\nu$-integrable, and assume there is a unit idele $t_0$ whose finite component (the second component of the underlying adele) equals $1$ and with $h(t_0) \neq 0$. Then there exists $u$ in the infinite adele ring $K_\infty$ such that $$\int \psi_K\big((t_\infty u,\,0)\big)\, h(t)\, d\nu(t) \neq 0,$$ where $t_\infty$ denotes the infinite component of the adele underlying $t$ and $\psi_K =$ `stdAddChar K` is the additive character $\psi_{\mathbb{Q}} \circ \mathrm{Tr}$ of $\mathbb{A}_K$ attached to the adelic trace data of $K$.
--
--   This is the statement that a non-trivial continuous integrable function on the idele group, integrated against the measure supported on ideles with trivial finite part, cannot be annihilated by all archimedean additive twists; it is an idelic packaging of the injectivity of the Fourier transform on $K_\infty = K \otimes_{\mathbb{Q}} \mathbb{R}$, using the non-degeneracy of the trace form on the mixed space and the comparison of `sPartMeasure K ∅` with Lebesgue measure twisted by the inverse norm density. It is used in the Rankin–Selberg part of the development, to produce an archimedean translate for which an integral against a torus integral of Whittaker coefficients is non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty
    (K : Type) [Field K] [NumberField K]
    (h : (AdeleRing (𝓞 K) K)ˣ → ℂ) (_hc : Continuous h)
    (_hint : Integrable h (NumberField.Idele.sPartMeasure K ∅))
    (_hne : ∃ t₀ : (AdeleRing (𝓞 K) K)ˣ, ((t₀ : AdeleRing (𝓞 K) K)).2 = 1 ∧ h t₀ ≠ 0) :
    ∃ u : InfiniteAdeleRing K,
      ∫ t, NumberField.StandardAddChar.stdAddChar K ((((t : AdeleRing (𝓞 K) K)).1 * u, 0)) * h t
          ∂(NumberField.Idele.sPartMeasure K ∅) ≠ 0 := by sorry
