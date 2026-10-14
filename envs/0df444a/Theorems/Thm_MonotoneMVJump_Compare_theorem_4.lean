-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_theorem_4
-- name    : MonotoneMVJump.Compare.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:12.781535+00:00
-- url     : https://prove2.me/theorems/52d165bd-7d0a-4ece-98b0-05aec203cad3
-- title:
--   Theorem 4 — the control (25) and $V(x,y,z,t)=-x+G(z,t)y$ solve the MMV Problem 1
-- statement:
--   Assume the standing market assumptions, the Conditions of Proposition 1, a solution $G$ of (20), initial data $t<T$, $z$ with factor path $Z=Z^{z,t}$, and Assumption 1 at $(z,t)$. Let $x\in\mathbb R$ and $y>0$. Then the candidate control (25) solves Problem 1. Precisely, there exist:
--   1. $(\eta^*,\phi^*)\in\mathcal M^t$, equal to (25) on $[t,T]$, with stochastic exponential $\mathcal E$ (so $Y^{\eta^*,\phi^*}=y\mathcal E$);
--   2. $\pi^*\in\mathcal A$, equal on $[t,T]$ to $\pi^*_s=-\frac{2Y_{s-}G(Z_s,s)}{\Sigma(Z_s)}\big[\mu(Z_s)-r-\sigma(Z_s)b(Z_s)\rho_W\frac{G_z(Z_s,s)}{G(Z_s,s)}\big]$, with wealth $X^{\pi^*}$.
--
--   They satisfy the saddle inequalities and the value identity
--   $$J^{\pi^*,\eta,\phi}(x,y,z,t)\le -x+G(z,t)y\le J^{\pi,\eta^*,\phi^*}(x,y,z,t)\qquad(\pi\in\mathcal A,\ (\eta,\phi)\in\mathcal M^t),$$
--   $$V(x,y,z,t)=\inf_{\pi}\sup_{\eta,\phi}J^{\pi,\eta,\phi}(x,y,z,t)=-x+G(z,t)y=J^{\pi^*,\eta^*,\phi^*}(x,y,z,t).$$
--   Moreover, for every $s\in[t,T]$, almost surely, $\pi^*_s=-\frac{X^{\pi^*}_{s-}-x+2yG(z,t)}{\Sigma(Z_s)}\big[\mu(Z_s)-r-\sigma(Z_s)b(Z_s)\rho_W\frac{G_z(Z_s,s)}{G(Z_s,s)}\big]$.
--
--   This is the solution of the MMV portfolio problem as a stochastic differential game. With $y=1/(2\theta)$ it gives the optimal MMV strategy.
--
--   **Formalization Note** The theorem's clause "satisfy Conditions of Theorem 1" (the HJBI verification route) is replaced by its conclusion, the saddle point and value. The value is an infimum and supremum in the extended reals. The verbatim cites the PDE (20) for $G$; here $G$ is a hypothesis in the bounded class of `MonotoneMVJump.Compare.PDE`.
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 17, Theorem 4, (25)–(26); conclusion of Theorem 1, pp. 8–9

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- Theorem 4 (p. 17): under Assumption 1, for `y > 0` the candidate control (25) exists and solves
Problem 1: there are `(η*, ϕ*) ∈ ℳ^t` given by (25) with stochastic exponential `ℰ`
(`Y^{η*,ϕ*} = y ℰ`), and an admissible `π* ∈ 𝒜` given by (25) with wealth `X^{π*}`, such that
`J^{π*,η,ϕ} ≤ −x + G(z, t) y ≤ J^{π,η*,ϕ*}` for all `π ∈ 𝒜`, `(η, ϕ) ∈ ℳ^t`, the value of
Problem 1 is `V(x, y, z, t) = −x + G(z, t) y = J^{π*,η*,ϕ*}`, and `π*` has the `X`-form. -/
theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (hP1 : PropOneConditions M) (G : ℝ → ℝ → ℝ) (hG : IsGSolution M G)
    (t : ℝ≥0) (ht : t < M.T) (z : ℝ) (Z : ℝ≥0 → Ω → ℝ) (hZ : M.IsFactor t z Z)
    (hA1 : Assumption1 M G t Z) (x y : ℝ) (hy : 0 < y) :
    ∃ (π η₁ η₂ : ℝ≥0 → Ω → ℝ) (ϕ : ℝ≥0 → Ω → ℝ → ℝ) (E X : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T →
        η₁ s ω = etaStar1 M G Z s ω ∧ η₂ s ω = etaStar2 M G Z s ω ∧
          (∀ p, ϕ s ω p = phiStar M G Z s ω p) ∧ π s ω = mmvStrategyY M G y Z E s ω) ∧
      M.InMt t η₁ η₂ ϕ E ∧ M.AdmA t x Z π X ∧
      (∀ (π' X' η₁' η₂' : ℝ≥0 → Ω → ℝ) (ϕ' : ℝ≥0 → Ω → ℝ → ℝ) (E' : ℝ≥0 → Ω → ℝ),
        M.AdmA t x Z π' X' → M.InMt t η₁' η₂' ϕ' E' →
          M.J y X E' ≤ -x + G z t * y ∧ -x + G z t * y ≤ M.J y X' E) ∧
      M.problem1Value t x y Z = ((-x + G z t * y : ℝ) : EReal) ∧
      M.J y X E = -x + G z t * y ∧
      ∀ s : ℝ≥0, t ≤ s → s ≤ M.T → ∀ᵐ ω ∂M.P,
        π s ω = mmvStrategyX M G x y z t Z X s ω := by sorry

end MonotoneMVJump.Compare
