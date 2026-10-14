-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_eq_39
-- name    : MonotoneMVJump.Compare.eq_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:12.884496+00:00
-- url     : https://prove2.me/theorems/9a752816-a2d4-47d0-9a15-af10a5434f17
-- title:
--   (39) — the optimal control of the MV Problem 2
-- statement:
--   Assume the standing market assumptions, the Conditions of Proposition 1, a solution $G$ of (20), initial data $t<T$, $z$ with factor path $Z$, $\theta>0$, $x\in\mathbb R$, and $R$ solving (38) with $\mathbb E[R_T]\ne1$ and $\mathrm{Var}[R_T]>0$. Consider the feedback (39):
--   $$\pi^*_s=-\frac{X^{\pi^*}_{s-}-x-\frac1\theta\cdot\frac{1-\mathbb E_{z,t}[R_T]}{\mathrm{Var}_{z,t}[R_T]}}{\Sigma(Z_s)}\Big[\mu(Z_s)-r+\sigma(Z_s)b(Z_s)\rho_W\frac{H_z(Z_s,s)}{H(Z_s,s)}\Big],\qquad t\le s\le T.$$
--   Then an admissible pair $(\pi^*,X^{\pi^*})$, $\pi^*\in\mathcal B_{x,z,t}$, following (39) exists. Every such pair is optimal for Problem 2:
--   $$U_\theta(X^{\pi^*}_T)=\sup_{\pi\in\mathcal B_{x,z,t}}U_\theta(X^\pi_T).$$
--
--   This is the optimal mean-variance strategy in the jump-diffusion market with stochastic factor.
--
--   **Formalization Note** The supremum is in the extended reals. $\mathbb E[R_T]\ne1$ and $\mathrm{Var}[R_T]>0$ make explicit the division in (39).
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 23, (39)

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- (39), p. 23: the optimal control of Problem 2 is the feedback (39): a feedback pair
`(π*, X^{π*})` of (39) exists in `ℬ_{x,z,t}`, and every such pair attains the optimal MV utility,
`U_θ(X^{π*}_T) = sup_{π ∈ ℬ} U_θ(X^π_T)`. -/
theorem eq_39 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (hP1 : PropOneConditions M) (G : ℝ → ℝ → ℝ) (hG : IsGSolution M G)
    (t : ℝ≥0) (ht : t < M.T) (z : ℝ) (Z : ℝ≥0 → Ω → ℝ) (hZ : M.IsFactor t z Z)
    (θ : ℝ) (hθ : 0 < θ) (x : ℝ) (R : ℝ≥0 → Ω → ℝ) (hR : IsRProcess M G t Z R)
    (hER : ∫ ω, R M.T ω ∂M.P ≠ 1) (hVar : 0 < variance (R M.T) M.P) :
    (∃ π X : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T →
          π s ω = mvStrategy39 M G (Dstar M.P θ x R M.T) Z X s ω) ∧ M.AdmB t x Z π X) ∧
      ∀ π X : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T →
          π s ω = mvStrategy39 M G (Dstar M.P θ x R M.T) Z X s ω) → M.AdmB t x Z π X →
        ((M.mvU θ (X M.T) : ℝ) : EReal) = M.mvValue t θ x Z := by sorry

end MonotoneMVJump.Compare
