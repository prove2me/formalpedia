-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_theorem_6_2
-- name    : MeanFieldPDE.Classical.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:51.731762+00:00
-- url     : https://prove2.me/theorems/f3f8e83a-8d38-408b-a89c-4cf0f314b6b6
-- title:
--   Theorem 6.2, p. 34 — the value function is the unique C^{1,(2,1)} solution of the mean-field PDE (6.12)
-- statement:
--   Suppose $\Phi\in C^{2,1}_b(\mathbb R^d\times\mathcal P_2(\mathbb R^d))$ and that the coefficients $\sigma,b$ are Lipschitz and satisfy Hypothesis (H.2). Then:
--
--   1. the value function $V(t,x,P_\xi)=E[\Phi(X_T^{t,x,P_\xi},P_{X_T^{t,\xi}})]$ is well defined on $[0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d)$: for every $\xi\in L^2(\mathcal F_t;\mathbb R^d)$ it equals $E[\Phi(X_T^{t,x,\xi},P_{X_T^{t,\xi}})]$;
--   2. $V\in C^{1,(2,1)}_b([0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d))$ and $V$ solves
--   $$\begin{aligned}0={}&\partial_tV(t,x,\mu)+\sum_{i=1}^d\partial_{x_i}V(t,x,\mu)b_i(x,\mu)+\tfrac12\sum_{i,j,k=1}^d\partial^2_{x_ix_j}V(t,x,\mu)(\sigma_{i,k}\sigma_{j,k})(x,\mu)\\&+\int\Big[\sum_{i=1}^d(\partial_\mu V)_i(t,x,\mu,y)b_i(y,\mu)+\tfrac12\sum_{i,j,k=1}^d\partial_{y_i}(\partial_\mu V)_j(t,x,\mu,y)(\sigma_{i,k}\sigma_{j,k})(y,\mu)\Big]\mu(dy),\\V(T,x,\mu)={}&\Phi(x,\mu),\end{aligned}$$
--   for all $(t,x,\mu)\in[0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d)$;
--   3. every $U\in C^{1,(2,1)}_b([0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d))$ solving (6.12) equals $V$ on $[0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d)$.
--
--   This identifies the value function of a McKean–Vlasov diffusion as the unique classical solution of the associated PDE on the Wasserstein space, without passing through a particle approximation.
--
--   **Formalization Note** The page writes $\Phi\in C^{2,1}$ and $C^{1,(2,1)}$ without the subscript $b$; the paper defines only the bounded classes ($\S5$ standing assumption on $\Phi$; Theorem 6.1 for the time-dependent class), which are used. $\tilde E$ over $\tilde\xi$ of law $\mu$ is the integral against $\mu$. The solution families of (3.1)–(3.2) are hypotheses; the companion theorem `well_posedness` states that they exist. Hypothesis (H.2) includes that $\sigma$ and $b$ are bounded on $\mathbb R^d\times\mathcal P_2(\mathbb R^d)$ (the $C^1_b(\mathbb R^d)$ of (H.1) ii), as the paper's proofs use it; see the `Lions` definition).
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 34, Theorem 6.2, (6.12)

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- Theorem 6.2, p. 34 (main result): suppose `Φ ∈ C^{2,1}_b(ℝ^d × P₂(ℝ^d))` and (H.2). Then
(a) the value function `V(t, x, P_ξ) = E[Φ(X^{t,x,P_ξ}_T, P_{X^{t,ξ}_T})]` is well defined on
`[0, T] × ℝ^d × P₂(ℝ^d)`: for every `ξ ∈ L²(F_t; ℝ^d)` it equals `E[Φ(X^{t,x,ξ}_T, P_{X^{t,ξ}_T})]`;
(b) `V ∈ C^{1,(2,1)}_b([0, T] × ℝ^d × P₂(ℝ^d))` and solves the PDE (6.12) with terminal value `Φ`;
(c) `V` is the unique solution of (6.12) in that class. -/
theorem theorem_6_2 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b) (hH2 : IsH2 P σ b)
    (Φ : E d → Measure (E d) → ℝ) (hΦ : IsC21b P Φ)
    (Xξ : ℝ≥0 → (Ω → E d) → ℝ≥0 → Ω → E d)
    (Xx : ℝ≥0 → E d → (Ω → E d) → ℝ≥0 → Ω → E d)
    (hXξ : IsMVFamily hS σ b Xξ) (hXx : IsDecFamily hS σ b Xξ Xx) :
    (∀ t ≤ T, ∀ (x : E d) (ξ : Ω → E d), IsL2At hS t ξ →
      valueFn F₀ P T Φ Xξ Xx t x (P.map ξ) = ∫ ω, Φ (Xx t x ξ T ω) (P.map (Xξ t ξ T)) ∂P) ∧
    (∃ (Dt : ℝ≥0 → E d → Measure (E d) → ℝ) (D : ℝ≥0 → Deriv2 d),
      IsC121bWith P T (valueFn F₀ P T Φ Xξ Xx) Dt D ∧ SolvesPDE σ b Φ T (valueFn F₀ P T Φ Xξ Xx) Dt D) ∧
    (∀ (U : ℝ≥0 → E d → Measure (E d) → ℝ) (Dt : ℝ≥0 → E d → Measure (E d) → ℝ)
        (D : ℝ≥0 → Deriv2 d), IsC121bWith P T U Dt D → SolvesPDE σ b Φ T U Dt D →
        ∀ t ≤ T, ∀ (x : E d) (μ : Measure (E d)), IsP2 μ → U t x μ = valueFn F₀ P T Φ Xξ Xx t x μ) := by sorry

end MeanFieldPDE.Classical
