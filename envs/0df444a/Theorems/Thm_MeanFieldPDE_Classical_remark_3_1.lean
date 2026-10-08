-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_remark_3_1
-- name    : MeanFieldPDE.Classical.remark_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:57.279415+00:00
-- url     : https://prove2.me/theorems/402e9b0f-f9be-4b9b-aaf2-adeb37b6e922
-- title:
--   Remark 3.1, p. 10 — X^{t,x,ξ₁} and X^{t,x,ξ₂} are indistinguishable when P_{ξ₁} = P_{ξ₂}
-- statement:
--   Assume the coefficients $\sigma,b$ are Lipschitz. Given $(t,x)\in[0,T]\times\mathbb R^d$, if $\xi_1,\xi_2\in L^2(\mathcal F_t;\mathbb R^d)$ have the same law, $P_{\xi_1}=P_{\xi_2}$, then
--   $$X^{t,x,\xi_1}_s=X^{t,x,\xi_2}_s\quad\text{for all }s\in[t,T],\ P\text{-a.s.}$$
--
--   This justifies the notation $X^{t,x,P_\xi}:=X^{t,x,\xi}$ (3.15) and makes the value function a function of the law.
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 10, Remark 3.1

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- Remark 3.1, p. 10: given `(t, x) ∈ [0, T] × ℝ^d`, the processes `X^{t,x,ξ₁}` and `X^{t,x,ξ₂}` are
indistinguishable on `[t, T]` whenever `ξ₁, ξ₂ ∈ L²(F_t; ℝ^d)` have the same law. -/
theorem remark_3_1 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b) :
    ∀ t ≤ T, ∀ (x : E d) (ξ₁ ξ₂ : Ω → E d) (X₁ X₂ Y₁ Y₂ : ℝ≥0 → Ω → E d),
      IsL2At hS t ξ₁ → IsL2At hS t ξ₂ → P.map ξ₁ = P.map ξ₂ →
      SolvesMV hS σ b t ξ₁ X₁ → SolvesMV hS σ b t ξ₂ X₂ →
      SolvesDec hS σ b t (fun _ => x) X₁ Y₁ → SolvesDec hS σ b t (fun _ => x) X₂ Y₂ →
      ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc t T, Y₁ s ω = Y₂ s ω := by sorry

end MeanFieldPDE.Classical
