-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_theorem_6_1
-- name    : MeanFieldPDE.Classical.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:06.665599+00:00
-- url     : https://prove2.me/theorems/b81b449d-1cff-46cf-bc98-eedc2045df22
-- title:
--   Theorem 6.1, p. 33 — time-dependent mean-field Itô formula (6.7) for F ∈ C^{1,(2,1)}_b([0,T] × ℝ^d × P₂(ℝ^d))
-- statement:
--   Let $F\in C^{1,(2,1)}_b([0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d))$ and let the coefficients be Lipschitz and satisfy (H.2). For $0\le t\le s\le T$, $x\in\mathbb R^d$ and $\xi\in L^2(\mathcal F_t;\mathbb R^d)$, with $X=X^{t,\xi}$, $Y=X^{t,x,P_\xi}$ and $\mu_r=P_{X_r}$, almost surely
--   $$F(s,Y_s,\mu_s)-F(t,x,P_\xi)=\int_t^s\big(\partial_rF(r,Y_r,\mu_r)+\mathcal LF(r,Y_r,\mu_r)\big)\,dr+\int_t^s\sum_{i,j=1}^d\partial_{x_i}F(r,Y_r,\mu_r)\sigma_{i,j}(Y_r,\mu_r)\,dB^j_r,$$
--   $s\in[t,T]$, where $\mathcal LF(r,\cdot,\cdot)$ is the operator of Proposition 6.1 applied to $F(r,\cdot,\cdot)$.
--
--   Both halves of the proof of Theorem 6.2 apply this formula, to the value function and to an arbitrary classical solution.
--
--   **Formalization Note** The page writes $\mathcal P(\mathbb R^d)$ for $\mathcal P_2(\mathbb R^d)$. The class $C^{1,(2,1)}_b$ includes the disclosed joint continuity of the derivatives entering the formula (see the `Lions` definition). The stochastic integrals are asserted to exist. Hypothesis (H.2) includes that $\sigma$ and $b$ are bounded on $\mathbb R^d\times\mathcal P_2(\mathbb R^d)$ (the $C^1_b(\mathbb R^d)$ of (H.1) ii), as the paper's proofs use it; see the `Lions` definition).
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 33, Theorem 6.1, (6.7)

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- Theorem 6.1, p. 33 (time-dependent mean-field Itô formula (6.7)): let
`F ∈ C^{1,(2,1)}_b([0, T] × ℝ^d × P₂(ℝ^d))` with time derivative `Dt` and spatial derivatives `D`;
under (H.2), for all `0 ≤ t ≤ s ≤ T`, `x ∈ ℝ^d`, `ξ ∈ L²(F_t; ℝ^d)`, writing `X = X^{t,ξ}`,
`Y = X^{t,x,P_ξ}` and `μ_r = P_{X_r}`, almost surely
`F(s, Y_s, μ_s) − F(t, x, P_ξ) = ∫_t^s (∂_rF(r, Y_r, μ_r) + (generator)(r, Y_r, μ_r)) dr
  + Σ_{i,j} ∫_t^s ∂_{x_i}F(r, Y_r, μ_r) σ_{i,j}(Y_r, μ_r) dB^j_r`. -/
theorem theorem_6_1 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d)
    (hLip : IsLipCoeff σ b) (hH2 : IsH2 P σ b)
    (F : ℝ≥0 → E d → Measure (E d) → ℝ) (Dt : ℝ≥0 → E d → Measure (E d) → ℝ)
    (D : ℝ≥0 → Deriv2 d) (hF : IsC121bWith P T F Dt D) :
    ∀ t ≤ T, ∀ (x : E d) (ξ : Ω → E d) (X Y : ℝ≥0 → Ω → E d), IsL2At hS t ξ →
      SolvesMV hS σ b t ξ X → SolvesDec hS σ b t (fun _ => x) X Y →
      ∃ J : Fin d → ℝ≥0 → Ω → ℝ,
        (∀ j : Fin d, Peng1990.SMP.IsItoIntegral (filt hS) P T (fun r ω => B r ω j)
          (fun r ω => if t < r ∧ r ≤ T then
            ∑ i, (D r).Dx (Y r ω) (P.map (X r)) i * σ (Y r ω) (P.map (X r)) i j else 0) (J j)) ∧
        ∀ s, t ≤ s → s ≤ T → ∀ᵐ ω ∂P,
          IntegrableOn (fun r : ℝ => Dt r.toNNReal (Y r.toNNReal ω) (P.map (X r.toNNReal))
            + generator σ b (D r.toNNReal) (Y r.toNNReal ω) (P.map (X r.toNNReal))) (Set.Icc (t : ℝ) s) ∧
          F s (Y s ω) (P.map (X s)) - F t x (P.map ξ) =
            (∫ r in Set.Icc (t : ℝ) s, Dt r.toNNReal (Y r.toNNReal ω) (P.map (X r.toNNReal))
            + generator σ b (D r.toNNReal) (Y r.toNNReal ω) (P.map (X r.toNNReal))) + ∑ j, (J j s ω - J j t ω) := by sorry

end MeanFieldPDE.Classical
