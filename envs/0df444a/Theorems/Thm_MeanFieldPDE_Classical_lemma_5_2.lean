-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_lemma_5_2
-- name    : MeanFieldPDE.Classical.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:20.134743+00:00
-- url     : https://prove2.me/theorems/0293a7d8-6afd-4018-b47e-054e40fc8c5c
-- title:
--   Lemma 5.2, p. 28 — V(t,·,·) ∈ C^{2,1}(ℝ^d × P₂(ℝ^d)), symmetric mixed derivatives, estimates (5.19)
-- statement:
--   Suppose the coefficients are Lipschitz and satisfy Hypothesis (H.2), and $\Phi\in C^{2,1}_b(\mathbb R^d\times\mathcal P_2(\mathbb R^d))$. Then for all $t\in[0,T]$, $V(t,\cdot,\cdot)\in C^{2,1}(\mathbb R^d\times\mathcal P_2(\mathbb R^d))$, the mixed second-order derivatives are symmetric,
--   $$\partial_{x_i}\big(\partial_\mu V(t,x,\mu,y)\big)=\partial_\mu\big(\partial_{x_i}V(t,x,\mu)\big)(y),\qquad1\le i\le d,$$
--   and for
--   $$U(t,x,\mu,y,z)=\big(\partial^2_{x_ix_j}V(t,x,\mu),\ \partial_{x_i}(\partial_\mu V(t,x,\mu,y)),\ \partial^2_\mu V(t,x,\mu,y,z),\ \partial_y(\partial_\mu V(t,x,\mu,y))\big)$$
--   there is a constant $C$ such that for all $t,t'\in[0,T]$, $x,x',y,y',z,z'\in\mathbb R^d$, $\mu,\mu'\in\mathcal P_2(\mathbb R^d)$:
--
--   1. $|U(t,x,\mu,y,z)|\le C$;
--   2. $|U(t,x,\mu,y,z)-U(t,x',\mu',y',z')|\le C(|x-x'|+|y-y'|+|z-z'|+W_2(\mu,\mu'))$;
--   3. $|U(t,x,\mu,y,z)-U(t',x,\mu,y,z)|\le C|t-t'|^{1/2}$.
--
--   These second-order estimates complete the spatial regularity of $V$ needed for the Itô formula.
--
--   **Formalization Note** The page prints $\Phi\in C^{2,1}$, the standing assumption of §5 is $C^{2,1}_b$, which is used. The page's (5.19) ii) omits the constant $C$ and the term $|z-z'|$ and quantifies over $\mathbb R$; the corrected statement is used (without $|z-z'|$ the bound would fail for $\partial^2_\mu V$, which depends on $z$). Bounds are stated componentwise on the vector-valued entries of $U$, which is equivalent up to the constant. Hypothesis (H.2) includes that $\sigma$ and $b$ are bounded on $\mathbb R^d\times\mathcal P_2(\mathbb R^d)$ (the $C^1_b(\mathbb R^d)$ of (H.1) ii), as the paper's proofs use it; see the `Lions` definition).
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 28, Lemma 5.2, (5.19)

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- Lemma 5.2, p. 28: under (H.2) and `Φ ∈ C^{2,1}_b(ℝ^d × P₂(ℝ^d))`, for all `t ∈ [0, T]`,
`V(t, ·, ·) ∈ C^{2,1}(ℝ^d × P₂(ℝ^d))`, the mixed second-order derivatives are symmetric,
`∂_{x_i}(∂_μV(t, x, μ, y)) = ∂_μ(∂_{x_i}V(t, x, μ))(y)`, and the second-order derivatives
`U = (∂²_{x_i x_j}V, ∂_{x_i}(∂_μV), ∂²_μV, ∂_y(∂_μV))` satisfy, for some constant `C` and all
`t, t' ∈ [0, T]`, `x, x', y, y', z, z' ∈ ℝ^d`, `μ, μ' ∈ P₂(ℝ^d)`: i) `|U(t, x, μ, y, z)| ≤ C`;
ii) `|U(t, x, μ, y, z) − U(t, x', μ', y', z')| ≤ C(|x − x'| + |y − y'| + |z − z'| + W₂(μ, μ'))`;
iii) `|U(t, x, μ, y, z) − U(t', x, μ, y, z)| ≤ C|t − t'|^{1/2}` (5.19). -/
theorem lemma_5_2 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b) (hH2 : IsH2 P σ b)
    (Φ : E d → Measure (E d) → ℝ) (hΦ : IsC21b P Φ)
    (Xξ : ℝ≥0 → (Ω → E d) → ℝ≥0 → Ω → E d)
    (Xx : ℝ≥0 → E d → (Ω → E d) → ℝ≥0 → Ω → E d)
    (hXξ : IsMVFamily hS σ b Xξ) (hXx : IsDecFamily hS σ b Xξ Xx) :
    ∃ D : ℝ≥0 → Deriv2 d,
      (∀ t ≤ T, IsC21bWith P (valueFn F₀ P T Φ Xξ Xx t) (D t)) ∧
      (∀ t ≤ T, ∀ (x : E d) (μ : Measure (E d)) (y : E d), IsP2 μ → ∀ i j : Fin d,
        (D t).DxDμ x μ y j i = (D t).DμDx x μ i y j) ∧
      ∃ C : ℝ, ∀ t ≤ T, ∀ t' ≤ T, ∀ (x x' y y' z z' : E d) (μ μ' : Measure (E d)),
        IsP2 μ → IsP2 μ' → ∀ k : Fin d,
          (‖(D t).Dxx x μ k‖ ≤ C ∧ ‖(D t).DxDμ x μ y k‖ ≤ C ∧
            ‖(D t).Dμμ x μ y k z‖ ≤ C ∧ ‖(D t).DyDμ x μ y k‖ ≤ C) ∧
          (‖(D t).Dxx x μ k - (D t).Dxx x' μ' k‖
              ≤ C * (‖x - x'‖ + ‖y - y'‖ + ‖z - z'‖ + W2 μ μ') ∧
            ‖(D t).DxDμ x μ y k - (D t).DxDμ x' μ' y' k‖
              ≤ C * (‖x - x'‖ + ‖y - y'‖ + ‖z - z'‖ + W2 μ μ') ∧
            ‖(D t).Dμμ x μ y k z - (D t).Dμμ x' μ' y' k z'‖
              ≤ C * (‖x - x'‖ + ‖y - y'‖ + ‖z - z'‖ + W2 μ μ') ∧
            ‖(D t).DyDμ x μ y k - (D t).DyDμ x' μ' y' k‖
              ≤ C * (‖x - x'‖ + ‖y - y'‖ + ‖z - z'‖ + W2 μ μ')) ∧
          (‖(D t).Dxx x μ k - (D t').Dxx x μ k‖ ≤ C * |(t : ℝ) - t'| ^ (1 / 2 : ℝ) ∧
            ‖(D t).DxDμ x μ y k - (D t').DxDμ x μ y k‖ ≤ C * |(t : ℝ) - t'| ^ (1 / 2 : ℝ) ∧
            ‖(D t).Dμμ x μ y k z - (D t').Dμμ x μ y k z‖ ≤ C * |(t : ℝ) - t'| ^ (1 / 2 : ℝ) ∧
            ‖(D t).DyDμ x μ y k - (D t').DyDμ x μ y k‖ ≤ C * |(t : ℝ) - t'| ^ (1 / 2 : ℝ))
      := by sorry

end MeanFieldPDE.Classical
