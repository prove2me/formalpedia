-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_lemma_6_1
-- name    : MeanFieldPDE.Classical.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:10.85415+00:00
-- url     : https://prove2.me/theorems/90f42907-27ae-4229-ae43-ad3798f3cb5d
-- title:
--   Lemma 6.1, p. 33 — V ∈ C^{1,(2,1)}([0,T] × ℝ^d × P₂(ℝ^d)) and the estimates (6.8) of ∂_tV
-- statement:
--   Assume $\Phi\in C^{2,1}_b(\mathbb R^d\times\mathcal P_2(\mathbb R^d))$ and that the coefficients are Lipschitz and satisfy (H.2). Then $V\in C^{1,(2,1)}([0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d))$, and its time derivative satisfies, for some constant $C$ and all $t,t'\in[0,T]$, $x,x'\in\mathbb R^d$, $\mu,\mu'\in\mathcal P_2(\mathbb R^d)$:
--
--   1. $|\partial_tV(t,x,\mu)|\le C$;
--   2. $|\partial_tV(t,x,\mu)-\partial_tV(t,x',\mu')|\le C(|x-x'|+W_2(\mu,\mu'))$;
--   3. $$|\partial_tV(t,x,\mu)-\partial_tV(t',x,\mu)|\le C|t-t'|^{1/2}.$$
--
--   Together with Lemmas 5.1–5.2 this puts $V$ in the class where the Itô formula of Theorem 6.1 applies.
--
--   **Formalization Note** The page prints $\Phi\in C^{2,1}$ and $V\in C^{1,(2,1)}$; the paper defines only the bounded class $C^{1,(2,1)}_b$ (Theorem 6.1), which is used, together with the standing $C^{2,1}_b$ assumption of §5 on $\Phi$. Hypothesis (H.2) includes that $\sigma$ and $b$ are bounded on $\mathbb R^d\times\mathcal P_2(\mathbb R^d)$ (the $C^1_b(\mathbb R^d)$ of (H.1) ii), as the paper's proofs use it; see the `Lions` definition).
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 33, Lemma 6.1, (6.8)

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- Lemma 6.1, p. 33: under (H.2) and `Φ ∈ C^{2,1}_b(ℝ^d × P₂(ℝ^d))`,
`V ∈ C^{1,(2,1)}_b([0, T] × ℝ^d × P₂(ℝ^d))`, and its time derivative satisfies, for some constant `C`
and all `t, t' ∈ [0, T]`, `x, x' ∈ ℝ^d`, `μ, μ' ∈ P₂(ℝ^d)`: i) `|∂_tV(t, x, μ)| ≤ C`;
ii) `|∂_tV(t, x, μ) − ∂_tV(t, x', μ')| ≤ C(|x − x'| + W₂(μ, μ'))`;
iii) `|∂_tV(t, x, μ) − ∂_tV(t', x, μ)| ≤ C|t − t'|^{1/2}` (6.8). -/
theorem lemma_6_1 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b) (hH2 : IsH2 P σ b)
    (Φ : E d → Measure (E d) → ℝ) (hΦ : IsC21b P Φ)
    (Xξ : ℝ≥0 → (Ω → E d) → ℝ≥0 → Ω → E d)
    (Xx : ℝ≥0 → E d → (Ω → E d) → ℝ≥0 → Ω → E d)
    (hXξ : IsMVFamily hS σ b Xξ) (hXx : IsDecFamily hS σ b Xξ Xx) :
    ∃ (Dt : ℝ≥0 → E d → Measure (E d) → ℝ) (D : ℝ≥0 → Deriv2 d),
      IsC121bWith P T (valueFn F₀ P T Φ Xξ Xx) Dt D ∧
      ∃ C : ℝ, ∀ t ≤ T, ∀ t' ≤ T, ∀ (x x' : E d) (μ μ' : Measure (E d)), IsP2 μ → IsP2 μ' →
        |Dt t x μ| ≤ C ∧
        |Dt t x μ - Dt t x' μ'| ≤ C * (‖x - x'‖ + W2 μ μ') ∧
        |Dt t x μ - Dt t' x μ| ≤ C * |(t : ℝ) - t'| ^ (1 / 2 : ℝ) := by sorry

end MeanFieldPDE.Classical
