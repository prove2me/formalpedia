-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_theorem_8
-- name    : MonotoneMVJump.Compare.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:24.742978+00:00
-- url     : https://prove2.me/theorems/81c68bc3-3ce8-4955-b9a5-295a6e03318f
-- title:
--   Theorem 8 — under Assumption 1 the optimal MMV and MV strategies coincide
-- statement:
--   Assume the standing market assumptions, the Conditions of Proposition 1, a solution $G$ of (20), initial data $t<T$, $z$ with factor path $Z=Z^{z,t}$, Assumption 1 at $(z,t)$, $\theta>0$, $x\in\mathbb R$, and $R$ solving (38) with $\mathbb E[R_T]\ne1$, $\mathrm{Var}[R_T]>0$. Take $y=1/(2\theta)$. The optimal MMV strategy, in the rewritten form of Theorem 4,
--   $$-\frac{X_{s-}-x+2yG(z,t)}{\Sigma(Z_s)}\Big[\mu(Z_s)-r-\sigma(Z_s)b(Z_s)\rho_W\frac{G_z(Z_s,s)}{G(Z_s,s)}\Big],$$
--   and the optimal MV strategy (39),
--   $$-\frac{X_{s-}-x-\frac1\theta\cdot\frac{1-\mathbb E_{z,t}[R_T]}{\mathrm{Var}_{z,t}[R_T]}}{\Sigma(Z_s)}\Big[\mu(Z_s)-r+\sigma(Z_s)b(Z_s)\rho_W\frac{H_z(Z_s,s)}{H(Z_s,s)}\Big],$$
--   are the same function of the path $X$, the factor path $Z$, and $s\in[t,T]$.
--
--   So under Assumption 1, an MMV investor and an MV investor with the same $\theta$ invest identically.
--
--   **Formalization Note** The strategies are compared as feedback maps, which is how the proof states the claim (it reduces to (40)). Assumption 1 is kept as printed: it is what makes the first map the MMV optimum (Theorem 4), although the identity of the two maps does not use it.
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 25, Theorem 8 (and (40))

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- Theorem 8 (p. 25): under Assumption 1 and with `y = 1/(2θ)`, the optimal MMV strategy (the
`X`-form of Theorem 4) and the optimal MV strategy (39) are the same feedback of
`(X_{s−}, Z_s, s)` on `[t, T]`. -/
theorem theorem_8 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (hP1 : PropOneConditions M) (G : ℝ → ℝ → ℝ) (hG : IsGSolution M G)
    (t : ℝ≥0) (ht : t < M.T) (z : ℝ) (Z : ℝ≥0 → Ω → ℝ) (hZ : M.IsFactor t z Z)
    (hA1 : Assumption1 M G t Z) (θ : ℝ) (hθ : 0 < θ) (x : ℝ) (R : ℝ≥0 → Ω → ℝ)
    (hR : IsRProcess M G t Z R) (hER : ∫ ω, R M.T ω ∂M.P ≠ 1)
    (hVar : 0 < variance (R M.T) M.P) :
    ∀ (X : ℝ≥0 → Ω → ℝ) (s : ℝ≥0), t ≤ s → s ≤ M.T → ∀ ω,
      mmvStrategyX M G x (1 / (2 * θ)) z t Z X s ω
        = mvStrategy39 M G (Dstar M.P θ x R M.T) Z X s ω := by sorry

end MonotoneMVJump.Compare
