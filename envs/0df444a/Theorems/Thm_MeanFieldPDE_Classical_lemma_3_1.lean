-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_lemma_3_1
-- name    : MeanFieldPDE.Classical.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:54.183552+00:00
-- url     : https://prove2.me/theorems/be159ce8-5148-462b-bca3-0e4eb7d85cea
-- title:
--   Lemma 3.1, p. 9 — E[sup_s |X^{t,x₁,ξ₁}_s − X^{t,x₂,ξ₂}_s|^p] ≤ C_p(|x₁ − x₂|^p + W₂(P_{ξ₁}, P_{ξ₂})^p)
-- statement:
--   Assume the coefficients $\sigma,b$ are Lipschitz. For all $p\ge2$ there is a constant $C_p\ge0$, depending only on the coefficients, such that
--   $$E\Big[\sup_{s\in[t,T]}\big|X_s^{t,x_1,\xi_1}-X_s^{t,x_2,\xi_2}\big|^p\Big]\le C_p\big(|x_1-x_2|^p+W_2(P_{\xi_1},P_{\xi_2})^p\big)$$
--   for all $t\in[0,T]$, $x_1,x_2\in\mathbb R^d$ and $\xi_1,\xi_2\in L^2(\mathcal F_t;\mathbb R^d)$.
--
--   The estimate shows that $X^{t,x,\xi}$ depends on $\xi$ only through its law (Remark 3.1), so the value function lives on $[0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d)$.
--
--   **Formalization Note** The expectation of the supremum is a lower Lebesgue integral in $[0,\infty]$; the right side is embedded by `ENNReal.ofReal`. $C_p$ is chosen after $p$ and the coefficients and before $t,x_1,x_2,\xi_1,\xi_2$.
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 9, Lemma 3.1, (3.7)

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- Lemma 3.1, p. 9: for all `p ≥ 2` there is a constant `C_p ≥ 0` (depending only on the
coefficients, not on `t, x, ξ`) such that
`E[sup_{s ∈ [t,T]} |X^{t,x₁,ξ₁}_s − X^{t,x₂,ξ₂}_s|^p] ≤ C_p (|x₁ − x₂|^p + W₂(P_{ξ₁}, P_{ξ₂})^p)` (3.7)
for all `t ∈ [0, T]`, `x₁, x₂ ∈ ℝ^d`, `ξ₁, ξ₂ ∈ L²(F_t; ℝ^d)`. -/
theorem lemma_3_1 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b) :
    ∀ p : ℝ, 2 ≤ p → ∃ Cp : ℝ, 0 ≤ Cp ∧
      ∀ t ≤ T, ∀ (x₁ x₂ : E d) (ξ₁ ξ₂ : Ω → E d) (X₁ X₂ Y₁ Y₂ : ℝ≥0 → Ω → E d),
        IsL2At hS t ξ₁ → IsL2At hS t ξ₂ →
        SolvesMV hS σ b t ξ₁ X₁ → SolvesMV hS σ b t ξ₂ X₂ →
        SolvesDec hS σ b t (fun _ => x₁) X₁ Y₁ → SolvesDec hS σ b t (fun _ => x₂) X₂ Y₂ →
        ∫⁻ ω, ⨆ s ∈ Set.Icc t T, ‖Y₁ s ω - Y₂ s ω‖ₑ ^ p ∂P
          ≤ ENNReal.ofReal (Cp * (‖x₁ - x₂‖ ^ p + W2 (P.map ξ₁) (P.map ξ₂) ^ p)) := by sorry

end MeanFieldPDE.Classical
