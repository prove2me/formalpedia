-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_MellinUniqueness_eq_smul_of_forall_isAdmissibleTwist_mellin_eq
-- name    : LanglandsTunnell.Converse.MellinUniqueness.eq_smul_of_forall_isAdmissibleTwist_mellin_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/6a2fe594-6e35-52ce-9d6d-1dad0e224085
-- title:
--   Mellin uniqueness on the ideles of ℚ
-- statement:
--   Let $\mathbb{A}^\times$ denote the unit group of the adele ring of $\mathbb{Q}$, equipped with its Borel structure and the Haar measure `Idele.idelicHaar`, and write $|x| =$ `TateGlobal.ideleNorm` $x$, the real number attached to $x$ by the distributive Haar character of $\mathbb{A}$. Let $F_1,F_2,G_1,G_2 : \mathbb{A}^\times \to \mathbb{C}$, let $c \in \mathbb{C}$ and $\sigma_1,\sigma_2 \in \mathbb{R}$. Assume: $F_1$ and $F_2$ are measurable; $x \mapsto \|F_1(x)\|\,|x|^{\sigma-1}$ is integrable for every real $\sigma \ge \sigma_1$, and $x \mapsto \|F_2(x)\|\,|x|^{\sigma-1}$ is integrable for every real $\sigma \le \sigma_2$; for every monoid homomorphism $\chi : \mathbb{A}^\times \to \mathbb{C}^\times$ that is trivial on the image of $\mathbb{Q}^\times$, continuous, and satisfies $\|\chi(x)\| = 1$ for all $x$, there are a function $E : \mathbb{C} \to \mathbb{C}$, differentiable on all of $\mathbb{C}$ and bounded on every vertical strip $a \le \operatorname{Re} s \le b$, and reals $\tau_1,\tau_2$ with $E(s) = \int_{\mathbb{A}^\times} F_1(x)\chi(x)|x|^{s-1}$ for $\operatorname{Re} s > \tau_1$ and $E(s) = c\int_{\mathbb{A}^\times} F_2(x)\chi(x)|x|^{s-1}$ for $\operatorname{Re} s < \tau_2$; finally $G_1,G_2$ are continuous and, for almost every $x$, the family $q \mapsto F_i(qx)$ indexed by $q \in \mathbb{Q}^\times$ (embedded in $\mathbb{A}^\times$) has sum $G_i(x)$, $i=1,2$. The conclusion is $G_1 = c \cdot G_2$ as functions on $\mathbb{A}^\times$.
--
--   This is the uniqueness step of the adelic converse theorem: a continuous function on the idele class group is determined by the Mellin transforms of its defining kernel against all unitary idele class characters, so that matching functional equations force proportionality of the two periodisations $G_1$ and $G_2$. It is used in the construction of the automorphy datum from the functional equations of the twisted $L$-functions, via [`LanglandsTunnell.CubicInduction.nonempty_automorphyDatum31_of_zeta_fe`](thm.html#LanglandsTunnell.CubicInduction.nonempty_automorphyDatum31_of_zeta_fe).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_MellinUniqueness_eq_smul_of_forall_isAdmissibleTwist_mellin_eq.lean

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory
attribute [local instance] NumberField.Idele.ideleBorel in

theorem LanglandsTunnell.Converse.MellinUniqueness.eq_smul_of_forall_isAdmissibleTwist_mellin_eq
    (F₁ F₂ G₁ G₂ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (c : ℂ) (σ₁ σ₂ : ℝ)
    (_hF₁ : Measurable F₁) (_hF₂ : Measurable F₂)
    (_hi₁ : ∀ σ : ℝ, σ₁ ≤ σ → Integrable
      (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ‖F₁ x‖ * (TateGlobal.ideleNorm ℚ x : ℝ) ^ (σ - 1)) (Idele.idelicHaar ℚ))
    (_hi₂ : ∀ σ : ℝ, σ ≤ σ₂ → Integrable
      (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ‖F₂ x‖ * (TateGlobal.ideleNorm ℚ x : ℝ) ^ (σ - 1)) (Idele.idelicHaar ℚ))
    (_hfe : ∀ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ →
      ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ LanglandsTunnell.LDatum.BoundedOnStrips E ∧ ∃ τ₁ τ₂ : ℝ,
        (∀ s : ℂ, τ₁ < s.re → E s = ∫ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
            F₁ x * ((χ x : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ x : ℝ) : ℂ) ^ (s - 1) ∂(Idele.idelicHaar ℚ)) ∧
        (∀ s : ℂ, s.re < τ₂ → E s = c * ∫ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
            F₂ x * ((χ x : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ x : ℝ) : ℂ) ^ (s - 1) ∂(Idele.idelicHaar ℚ)))
    (_hG₁ : Continuous G₁) (_hG₂ : Continuous G₂)
    (_hp₁ : ∀ᵐ x ∂(Idele.idelicHaar ℚ), HasSum
      (fun q : ℚˣ => F₁ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q * x)) (G₁ x))
    (_hp₂ : ∀ᵐ x ∂(Idele.idelicHaar ℚ), HasSum
      (fun q : ℚˣ => F₂ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q * x)) (G₂ x)) :
    G₁ = c • G₂ := by sorry
