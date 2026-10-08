-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_proposition_6_1
-- name    : MeanFieldPDE.Classical.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:10.535111+00:00
-- url     : https://prove2.me/theorems/21e758b0-f0f9-487c-ac14-86f5871ee8c8
-- title:
--   Proposition 6.1, p. 31 — mean-field Itô formula (6.1) for Φ(X^{t,x,P_ξ}_s, P_{X^{t,ξ}_s}), Φ ∈ C^{2,1}_b
-- statement:
--   Let $\Phi\in C^{2,1}_b(\mathbb R^d\times\mathcal P_2(\mathbb R^d))$, and let the coefficients be Lipschitz and satisfy (H.2). For $0\le t\le s\le T$, $x\in\mathbb R^d$ and $\xi\in L^2(\mathcal F_t;\mathbb R^d)$, write $X=X^{t,\xi}$, $Y=X^{t,x,P_\xi}$ and $\mu_r=P_{X_r}$. Then almost surely
--   $$\Phi(Y_s,\mu_s)-\Phi(x,P_\xi)=\int_t^s\mathcal L\Phi(Y_r,\mu_r)\,dr+\int_t^s\sum_{i,j=1}^d\partial_{x_i}\Phi(Y_r,\mu_r)\sigma_{i,j}(Y_r,\mu_r)\,dB^j_r,\qquad s\in[t,T],$$
--   where
--   $$\mathcal L\Phi(y,\mu)=\sum_i\partial_{x_i}\Phi\,b_i(y,\mu)+\tfrac12\sum_{i,j,k}\partial^2_{x_ix_j}\Phi(\sigma_{i,k}\sigma_{j,k})(y,\mu)+\tilde E\Big[\sum_i(\partial_\mu\Phi)_i(y,\mu,\tilde X_r^{t,\tilde\xi})b_i(\tilde X_r^{t,\tilde\xi},\mu)+\tfrac12\sum_{i,j,k}\partial_{y_i}(\partial_\mu\Phi)_j(y,\mu,\tilde X_r^{t,\tilde\xi})(\sigma_{i,k}\sigma_{j,k})(\tilde X_r^{t,\tilde\xi},\mu)\Big]$$
--   and $\tilde X^{t,\tilde\xi}_r$ is an independent copy of $X_r$.
--
--   This is the chain rule for functions of the state and of the law of a McKean–Vlasov diffusion.
--
--   **Formalization Note** $\tilde E[\cdot]$ is the integral against the law $\mu_r$ of $X_r$. The page evaluates the last $\sigma\sigma$ factor at time $s$ inside the $dr$-integral; this is read $r$ (as in (6.7)). The conclusion asserts that the stochastic integrals exist (as Itô integrals of $1_{(t,T]}\sum_i\partial_{x_i}\Phi\,\sigma_{i,j}$ against $B^j$) and that the drift is integrable on $[t,s]$. Hypothesis (H.2) includes that $\sigma$ and $b$ are bounded on $\mathbb R^d\times\mathcal P_2(\mathbb R^d)$ (the $C^1_b(\mathbb R^d)$ of (H.1) ii), as the paper's proofs use it; see the `Lions` definition).
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 31, Proposition 6.1, (6.1)

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- Proposition 6.1, p. 31 (mean-field Itô formula (6.1)): let `Φ ∈ C^{2,1}_b(ℝ^d × P₂(ℝ^d))` with
derivatives `DΦ`; under (H.2), for all `0 ≤ t ≤ s ≤ T`, `x ∈ ℝ^d`, `ξ ∈ L²(F_t; ℝ^d)`, writing
`X = X^{t,ξ}`, `Y = X^{t,x,P_ξ}` and `μ_r = P_{X_r}`,
`Φ(Y_s, μ_s) − Φ(x, P_ξ) = ∫_t^s (generator)(Y_r, μ_r) dr + Σ_{i,j} ∫_t^s ∂_{x_i}Φ(Y_r, μ_r) σ_{i,j}(Y_r, μ_r) dB^j_r`
almost surely, the drift being integrable on `[t, s]`. The `Ẽ[·]` over `X̃^{t,ξ̃}_r` is the integral
against its law `μ_r` (inside `generator`). -/
theorem proposition_6_1 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b) (hH2 : IsH2 P σ b)
    (Φ : E d → Measure (E d) → ℝ) (DΦ : Deriv2 d) (hΦ : IsC21bWith P Φ DΦ) :
    ∀ t ≤ T, ∀ (x : E d) (ξ : Ω → E d) (X Y : ℝ≥0 → Ω → E d), IsL2At hS t ξ →
      SolvesMV hS σ b t ξ X → SolvesDec hS σ b t (fun _ => x) X Y →
      ∃ J : Fin d → ℝ≥0 → Ω → ℝ,
        (∀ j : Fin d, Peng1990.SMP.IsItoIntegral (filt hS) P T (fun r ω => B r ω j)
          (fun r ω => if t < r ∧ r ≤ T then
            ∑ i, DΦ.Dx (Y r ω) (P.map (X r)) i * σ (Y r ω) (P.map (X r)) i j else 0) (J j)) ∧
        ∀ s, t ≤ s → s ≤ T → ∀ᵐ ω ∂P,
          IntegrableOn (fun r : ℝ => generator σ b DΦ (Y r.toNNReal ω) (P.map (X r.toNNReal))) (Set.Icc (t : ℝ) s) ∧
          Φ (Y s ω) (P.map (X s)) - Φ x (P.map ξ) =
            (∫ r in Set.Icc (t : ℝ) s, generator σ b DΦ (Y r.toNNReal ω) (P.map (X r.toNNReal))) + ∑ j, (J j s ω - J j t ω) := by sorry

end MeanFieldPDE.Classical
