-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_lemma_5_1
-- name    : MeanFieldPDE.Classical.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:08.314981+00:00
-- url     : https://prove2.me/theorems/150d8f74-6435-4153-a9fe-bd25ecf5d962
-- title:
--   Lemma 5.1, (5.4), pp. 25–26 — V(t,·,·) ∈ C^{1,1}(ℝ^d × P₂(ℝ^d)): bounds, Lipschitz and ½-Hölder-in-t estimates of ∂_xV, ∂_μV
-- statement:
--   Suppose $\Phi\in C^{1,1}_b(\mathbb R^d\times\mathcal P_2(\mathbb R^d))$, the coefficients are Lipschitz and satisfy Hypothesis (H.1). Then $V(t,\cdot,\cdot)\in C^{1,1}(\mathbb R^d\times\mathcal P_2(\mathbb R^d))$ for all $t\in[0,T]$, with derivatives $\partial_xV$, $\partial_\mu V$, and there is a constant $C$ such that for all $t,t'\in[0,T]$, $x,x',y,y'\in\mathbb R^d$, $\mu,\mu'\in\mathcal P_2(\mathbb R^d)$ and $1\le i\le d$:
--
--   1. $|\partial_{x_i}V(t,x,\mu)|+|(\partial_\mu V)_i(t,x,\mu,y)|\le C$;
--   2. $|\partial_{x_i}V(t,x,\mu)-\partial_{x_i}V(t,x',\mu')|+|(\partial_\mu V)_i(t,x,\mu,y)-(\partial_\mu V)_i(t,x',\mu',y')|\le C(|x-x'|+|y-y'|+W_2(\mu,\mu'))$;
--   3. $$|V(t,x,\mu)-V(t',x,\mu)|+|\partial_{x_i}V(t,x,\mu)-\partial_{x_i}V(t',x,\mu)|+|(\partial_\mu V)_i(t,x,\mu,y)-(\partial_\mu V)_i(t',x,\mu,y)|\le C|t-t'|^{1/2}.$$
--
--   These are the first-order regularity estimates of the value function used for its Itô formula.
--
--   **Formalization Note** The paper's quantifier "$x,x',y,y'\in\mathbb R$" is its $d=1$ reduction; it is read $\mathbb R^d$. The representation formulas (5.2)–(5.3) of the derivatives are not part of this item. $\mu=P_\xi$ ranges over all of $\mathcal P_2$ because $\mathcal F_0\subset\mathcal F_t$ is rich. Hypothesis (H.1) includes that $\sigma$ and $b$ are bounded on $\mathbb R^d\times\mathcal P_2(\mathbb R^d)$ (the $C^1_b(\mathbb R^d)$ of (H.1) ii), as the paper's proofs use it; see the `Lions` definition).
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, pp. 25–26, Lemma 5.1, (5.4)

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- Lemma 5.1, estimates (5.4), pp. 25–26: if `Φ ∈ C^{1,1}_b(ℝ^d × P₂(ℝ^d))` and (H.1) holds, then
`V(t, ·, ·) ∈ C^{1,1}(ℝ^d × P₂(ℝ^d))` for all `t ∈ [0, T]`, and there is a constant `C` such that for all
`t, t' ∈ [0, T]`, `x, x', y, y' ∈ ℝ^d`, `μ, μ' ∈ P₂(ℝ^d)` and `1 ≤ i ≤ d`:
i) `|∂_{x_i}V(t, x, μ)| + |(∂_μV)_i(t, x, μ, y)| ≤ C`;
ii) `|∂_{x_i}V(t, x, μ) − ∂_{x_i}V(t, x', μ')| + |(∂_μV)_i(t, x, μ, y) − (∂_μV)_i(t, x', μ', y')|
  ≤ C(|x − x'| + |y − y'| + W₂(μ, μ'))`;
iii) `|V(t, x, μ) − V(t', x, μ)| + |∂_{x_i}V(t, x, μ) − ∂_{x_i}V(t', x, μ)|
  + |(∂_μV)_i(t, x, μ, y) − (∂_μV)_i(t', x, μ, y)| ≤ C|t − t'|^{1/2}`. -/
theorem lemma_5_1 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b) (hH1 : IsH1 P σ b)
    (Φ : E d → Measure (E d) → ℝ) (hΦ : IsC11b P Φ)
    (Xξ : ℝ≥0 → (Ω → E d) → ℝ≥0 → Ω → E d)
    (Xx : ℝ≥0 → E d → (Ω → E d) → ℝ≥0 → Ω → E d)
    (hXξ : IsMVFamily hS σ b Xξ) (hXx : IsDecFamily hS σ b Xξ Xx) :
    ∃ (DxV : ℝ≥0 → E d → Measure (E d) → E d) (DμV : ℝ≥0 → E d → Measure (E d) → E d → E d),
      (∀ t ≤ T, IsC11bWith P (valueFn F₀ P T Φ Xξ Xx t) (DxV t) (DμV t)) ∧
      ∃ C : ℝ, ∀ t ≤ T, ∀ t' ≤ T, ∀ (x x' y y' : E d) (μ μ' : Measure (E d)),
        IsP2 μ → IsP2 μ' → ∀ i : Fin d,
          |DxV t x μ i| + |DμV t x μ y i| ≤ C ∧
          |DxV t x μ i - DxV t x' μ' i| + |DμV t x μ y i - DμV t x' μ' y' i|
            ≤ C * (‖x - x'‖ + ‖y - y'‖ + W2 μ μ') ∧
          |valueFn F₀ P T Φ Xξ Xx t x μ - valueFn F₀ P T Φ Xξ Xx t' x μ|
              + |DxV t x μ i - DxV t' x μ i| + |DμV t x μ y i - DμV t' x μ y i|
            ≤ C * |(t : ℝ) - t'| ^ (1 / 2 : ℝ) := by sorry

end MeanFieldPDE.Classical
