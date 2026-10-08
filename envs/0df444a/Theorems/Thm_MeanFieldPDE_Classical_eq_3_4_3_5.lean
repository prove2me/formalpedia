-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_eq_3_4_3_5
-- name    : MeanFieldPDE.Classical.eq_3_4_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:59.544682+00:00
-- url     : https://prove2.me/theorems/f51c0228-6e0b-47a3-afb0-44a7401da8ab
-- title:
--   (3.4)–(3.5), §3, p. 8 — X^{t,x,ξ}|_{x=ξ} = X^{t,ξ} and the flow property of (X^{t,x,ξ}, X^{t,ξ})
-- statement:
--   Assume the coefficients $\sigma,b$ are Lipschitz.
--
--   1. (3.4) If $\xi\in L^2(\mathcal F_t;\mathbb R^d)$ and $Y$ solves the decoupled equation with initial value $\xi$ and the law flow of $X^{t,\xi}$,
--   $$Y_s=\xi+\int_t^s\sigma(Y_r,P_{X^{t,\xi}_r})\,dB_r+\int_t^sb(Y_r,P_{X^{t,\xi}_r})\,dr,$$
--   then $Y$ and $X^{t,\xi}$ are indistinguishable on $[t,T]$: $X^{t,x,\xi}|_{x=\xi}=X^{t,\xi}$.
--   2. (3.5) For $0\le t\le s\le T$, $x\in\mathbb R^d$ and $\xi\in L^2(\mathcal F_t;\mathbb R^d)$,
--   $$\big(X_r^{s,X_s^{t,x,\xi},X_s^{t,\xi}},X_r^{s,X_s^{t,\xi}}\big)=\big(X_r^{t,x,\xi},X_r^{t,\xi}\big),\qquad r\in[s,T],$$
--   indistinguishably, where $X^{s,X^{t,\xi}_s}$ solves (3.1) from $(s,X^{t,\xi}_s)$ and $X^{s,X_s^{t,x,\xi},X^{t,\xi}_s}$ solves the decoupled equation from $(s,X^{t,x,\xi}_s)$ with the law flow of $X^{s,X^{t,\xi}_s}$.
--
--   The flow property is what makes the value function a martingale along the dynamics.
--
--   **Formalization Note** The decoupled equation takes a random initial value directly, so (3.4) does not substitute a random variable into a family indexed by deterministic $x$. Solutions are arbitrary processes satisfying the solution predicates.
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 8, (3.4) and (3.5)

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- (3.4) and the flow property (3.5), §3, p. 8. (3.4): the solution of (3.2) with the initial
value `x` replaced by `ξ` is `X^{t,ξ}`: a solution `Y` of `Y_s = ξ + ∫_t^s σ(Y_r, P_{X^{t,ξ}_r}) dB_r
+ ∫_t^s b(Y_r, P_{X^{t,ξ}_r}) dr` is indistinguishable from `X^{t,ξ}` on `[t, T]`. (3.5): for
`0 ≤ t ≤ s ≤ T`, `x ∈ ℝ^d`, `ξ ∈ L²(F_t; ℝ^d)`, the solutions restarted at time `s` from
`(X^{t,x,ξ}_s, X^{t,ξ}_s)` coincide with `(X^{t,x,ξ}, X^{t,ξ})` on `[s, T]` (indistinguishably). -/
theorem eq_3_4_3_5 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b) :
    (∀ t ≤ T, ∀ (ξ : Ω → E d) (X Y : ℝ≥0 → Ω → E d), IsL2At hS t ξ →
      SolvesMV hS σ b t ξ X → SolvesDec hS σ b t ξ X Y →
      ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc t T, Y s ω = X s ω) ∧
    (∀ t s : ℝ≥0, t ≤ s → s ≤ T →
      ∀ (x : E d) (ξ : Ω → E d) (X Y X' Y' : ℝ≥0 → Ω → E d), IsL2At hS t ξ →
      SolvesMV hS σ b t ξ X → SolvesDec hS σ b t (fun _ => x) X Y →
      SolvesMV hS σ b s (X s) X' → SolvesDec hS σ b s (Y s) X' Y' →
      ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc s T, Y' r ω = Y r ω ∧ X' r ω = X r ω) := by sorry

end MeanFieldPDE.Classical
