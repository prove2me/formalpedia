-- Prove2me | Theorems.Thm_NumberField_Idele_integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg
-- name    : NumberField.Idele.integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/3242b755-72c6-55b9-a143-96ab0b9f6c2e
-- title:
--   Two-sided archimedean decay implies integrability for ν_∅
-- statement:
--   Let $K$ be a number field, $E$ a normed additive commutative group and $F \colon (\mathbb{A}_K)^\times \to E$ a function on the unit group of the adele ring of $\mathcal{O}_K$ in $K$, where the idele group carries its Borel $\sigma$-algebra. The measure in play is [`NumberField.Idele.sPartMeasure K ∅`](def/NumberField_IdeleProductMeasure.html#L458), the push-forward along the group homomorphism `Units.map (partAtAdele K ∅)` of the Haar measure `idelicHaar K` of the idele group restricted to the subgroup `unitIdelesOutside (𝓞 K) K ∅`, namely those ideles $\delta$ whose finite component satisfies, at every finite place $v$, that both $\delta_v$ and $(\delta^{-1})_v$ lie in the valuation ring of the completion at $v$. Assume $F$ is almost everywhere strongly measurable for this measure, and let $\delta, c, A$ be reals with $0 < \delta + c$ and $0 < \delta + 2c$. Assume two bounds, both only for ideles $a$ whose finite part is $1$: first, $\|F(a)\| \le A \cdot \|a\|^{c} \prod_{w \mid \infty} \min(1, \|a_w\|)^{\delta}$, where $\|a\|$ denotes `ideleNorm K a`, the value at $a$ of the distributive Haar character of the adele ring viewed as a real number, and $a_w$ is the component of the infinite part of $a$ at the infinite place $w$; second, for every natural number $M$ there is a real $B$ with $\|F(a)\| \le B \cdot \|a\|^{c} \|a_w\|^{-M}$ for all such $a$ and every infinite place $w$. The conclusion is that $F$ is integrable for `sPartMeasure K ∅`.
--
--   This is the convergence criterion for integrals over the archimedean part of the idele class group: a function bounded by a positive power of $\min(1,\|a_w\|)$ as a coordinate tends to $0$ and decaying faster than any polynomial as a single coordinate grows is integrable against the archimedean idelic measure. It is used in the treatment of global Rankin–Selberg integrals, for instance to establish analyticity in a neighbourhood of archimedean integrals over the torus and the existence of archimedean translates with non-vanishing Rankin–Selberg pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg
    (K : Type) [Field K] [NumberField K]
    {E : Type*} [NormedAddCommGroup E]
    (F : (AdeleRing (𝓞 K) K)ˣ → E)
    (_hF : AEStronglyMeasurable F (NumberField.Idele.sPartMeasure K ∅))
    (δ c A : ℝ) (_hδc : 0 < δ + c) (_hδc₂ : 0 < δ + 2 * c)
    (_hsmall : ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      ‖F a‖ ≤ A * NumberField.TateGlobal.ideleNorm K a ^ c *
        ∏ w : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ)
    (_hlarge : ∀ M : ℕ, ∃ B : ℝ, ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      ∀ w : InfinitePlace K,
        ‖F a‖ ≤ B * NumberField.TateGlobal.ideleNorm K a ^ c * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ (-(M : ℝ))) :
    Integrable F (NumberField.Idele.sPartMeasure K ∅) := by sorry
