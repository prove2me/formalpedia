-- Prove2me | Theorems.Thm_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap
-- name    : NumberField.AdelicBox.setIntegral_adelicBox_tsum_add_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/600b0d01-2f2a-595a-87e4-5f9b125b1bd7
-- title:
--   Unfolding an integrable function over the adelic box
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}_F = \mathrm{AdeleRing}(\mathcal{O}_F, F)$ carried by its Borel $\sigma$-algebra `adeleBorel` and equipped with the additive Haar measure $\mu =$ `adelicAddHaar`, and let $\Phi : \mathbb{A}_F \to \mathbb{C}$ be $\mu$-integrable. Write $B =$ `adelicBox F` for the set of adeles $x = (x_\infty, x_{\mathrm{fin}})$ whose infinite component lies in the preimage, under the ring equivalence of $\prod_{w} F_w$ with the mixed space of $F$, of the fundamental domain of the $\mathbb{Z}$-span of the lattice basis of $\mathcal{O}_F$ under the mixed embedding, and whose finite component satisfies $x_{\mathrm{fin}}(v) \in \mathcal{O}_{F_v}$ for every $v$ in the height-one spectrum of $\mathcal{O}_F$. The assertion is that $$\int_{B} \Big( \sum_{\xi \in F}^{\prime} \Phi\big(t + \iota(\xi)\big) \Big)\, d\mu(t) = \int_{\mathbb{A}_F} \Phi \, d\mu,$$ where $\iota$ is the algebra map $F \to \mathbb{A}_F$ and the inner sum is the unconditional sum over $F$ (interpreted as $0$ at those $t$ where the family is not summable).
--
--   This is the unfolding identity for the periodization of an integrable function along the discrete subgroup of principal adeles, the integral-level counterpart of the statement that the adelic box is a fundamental domain for $F \subset \mathbb{A}_F$. It is used in the adelic analysis of automorphic forms, for instance in the computation of constant terms of pseudo-Eisenstein series and in the estimates for Borel-type kernels against the adelic height.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_setIntegral_adelicBox_tsum_add_algebraMap.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain

theorem NumberField.AdelicBox.setIntegral_adelicBox_tsum_add_algebraMap (F : Type) [Field F]
    [NumberField F] (Φ : AdeleRing (𝓞 F) F → ℂ) (hΦ : Integrable Φ (adelicAddHaar (𝓞 F) F)) :
    ∫ t in adelicBox F, (∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ))
        ∂(adelicAddHaar (𝓞 F) F)
      = ∫ t, Φ t ∂(adelicAddHaar (𝓞 F) F) := by sorry
