-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_eq_6_20
-- name    : MeanFieldPDE.Classical.eq_6_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:00.928988+00:00
-- url     : https://prove2.me/theorems/6e71d995-708a-4f5f-b954-5fe6373abab3
-- title:
--   (6.19)–(6.20), proof of Theorem 6.2, pp. 35–36 — every C^{1,(2,1)} solution U of (6.12) equals V
-- statement:
--   Assume the coefficients are Lipschitz and satisfy (H.2), and $\Phi\in C^{2,1}_b(\mathbb R^d\times\mathcal P_2(\mathbb R^d))$. Let $U\in C^{1,(2,1)}_b([0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d))$ solve the PDE (6.12) with terminal value $U(T,\cdot,\cdot)=\Phi$. Then
--   $$U(t,x,\mu)=V(t,x,\mu)\qquad\text{for all }t\in[0,T],\ x\in\mathbb R^d,\ \mu\in\mathcal P_2(\mathbb R^d).$$
--
--   This is the uniqueness half of Theorem 6.2.
--
--   **Formalization Note** $U$ ranges over every function of the class with its own derivative witnesses, not only over expectations. Hypothesis (H.2) includes that $\sigma$ and $b$ are bounded on $\mathbb R^d\times\mathcal P_2(\mathbb R^d)$ (the $C^1_b(\mathbb R^d)$ of (H.1) ii), as the paper's proofs use it; see the `Lions` definition).
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, pp. 35–36, (6.19)–(6.20), proof of Theorem 6.2

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- (6.19)–(6.20), proof of Theorem 6.2, pp. 35–36 (uniqueness): under (H.2) and
`Φ ∈ C^{2,1}_b(ℝ^d × P₂(ℝ^d))`, every `U ∈ C^{1,(2,1)}_b([0, T] × ℝ^d × P₂(ℝ^d))` that solves the PDE
(6.12) with terminal value `Φ` coincides with the value function: `U(t, x, μ) = V(t, x, μ)` for all
`t ∈ [0, T]`, `x ∈ ℝ^d`, `μ ∈ P₂(ℝ^d)`. -/
theorem eq_6_20 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b) (hH2 : IsH2 P σ b)
    (Φ : E d → Measure (E d) → ℝ) (hΦ : IsC21b P Φ)
    (Xξ : ℝ≥0 → (Ω → E d) → ℝ≥0 → Ω → E d)
    (Xx : ℝ≥0 → E d → (Ω → E d) → ℝ≥0 → Ω → E d)
    (hXξ : IsMVFamily hS σ b Xξ) (hXx : IsDecFamily hS σ b Xξ Xx) :
    ∀ (U : ℝ≥0 → E d → Measure (E d) → ℝ) (Dt : ℝ≥0 → E d → Measure (E d) → ℝ)
        (D : ℝ≥0 → Deriv2 d), IsC121bWith P T U Dt D → SolvesPDE σ b Φ T U Dt D →
        ∀ t ≤ T, ∀ (x : E d) (μ : Measure (E d)), IsP2 μ → U t x μ = valueFn F₀ P T Φ Xξ Xx t x μ := by sorry

end MeanFieldPDE.Classical
