-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_theorem_3
-- name    : MonotoneMVJump.Compare.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:15.552295+00:00
-- url     : https://prove2.me/theorems/24c6c000-5459-47ff-b930-1dd96dc1cd25
-- title:
--   Theorem 3 — under the candidate control (19), $2Y_sG(Z_s,s)=X^{\pi^*}_s-x+2yG(z,t)$
-- statement:
--   Fix the market of `MonotoneMVJump.Compare.Market` under its standing assumptions and the Conditions of Proposition 1, a solution $G$ of (20) as in `MonotoneMVJump.Compare.PDE`, initial data $t<T$, $z$, the factor path $Z=Z^{z,t}$, wealth $x$ and $y>0$. Apply the candidate control (19) = (25). The stochastic exponential $\mathcal E$ solves (5) from $\mathcal E_t=1$ with $(\eta^*,\phi^*)$, and $Y^{\eta^*,\phi^*}=y\mathcal E$. The strategy $\pi^*_s=-\frac{2Y_{s-}G(Z_s,s)}{\Sigma(Z_s)}\big[\mu(Z_s)-r-\sigma(Z_s)b(Z_s)\rho_W\frac{G_z(Z_s,s)}{G(Z_s,s)}\big]$ holds on $[t,T]$, and $X^{\pi^*}$ is its wealth from $x$. Then for every $s\in[t,T]$, almost surely,
--   $$2Y^{\eta^*,\phi^*}_sG(Z_s,s)=X^{\pi^*}_s-x+2yG(z,t).$$
--
--   This identity links the market player's density process to the investor's wealth. It is how the optimal MMV strategy is rewritten in feedback form of wealth.
--
--   **Formalization Note** The processes are given, not constructed. Nothing about admissibility is assumed. The identity is stated almost surely for each fixed $s$.
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 15, Theorem 3, (24)

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- Theorem 3 (p. 15): under the candidate control (19) = (25) — `ℰ` solves (5) from `1` with
`(η*, ϕ*)`, `Y^{η*,ϕ*} = y ℰ`, `π*` is the `Y`-form of (25) and `X^{π*}` its wealth —
`2 Y^{η*,ϕ*}_s G(Z_s, s) = X^{π*}_s − x + 2y G(z, t)` a.s. for every `s ∈ [t, T]`. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (hP1 : PropOneConditions M) (G : ℝ → ℝ → ℝ) (hG : IsGSolution M G)
    (t : ℝ≥0) (ht : t < M.T) (z : ℝ) (Z : ℝ≥0 → Ω → ℝ) (hZ : M.IsFactor t z Z)
    (x y : ℝ) (hy : 0 < y) (π η₁ η₂ : ℝ≥0 → Ω → ℝ) (ϕ : ℝ≥0 → Ω → ℝ → ℝ)
    (E X : ℝ≥0 → Ω → ℝ)
    (hfb : ∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T →
      η₁ s ω = etaStar1 M G Z s ω ∧ η₂ s ω = etaStar2 M G Z s ω ∧
        (∀ p, ϕ s ω p = phiStar M G Z s ω p) ∧ π s ω = mmvStrategyY M G y Z E s ω)
    (hE : M.SolvesDD t 1 η₁ η₂ ϕ E) (hX : M.IsWealth t x Z π X) :
    ∀ s : ℝ≥0, t ≤ s → s ≤ M.T → ∀ᵐ ω ∂M.P,
      2 * (y * E s ω) * G (Z s ω) s = X s ω - x + 2 * y * G z t := by sorry

end MonotoneMVJump.Compare
