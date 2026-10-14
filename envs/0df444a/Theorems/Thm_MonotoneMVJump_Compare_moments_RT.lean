-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_moments_RT
-- name    : MonotoneMVJump.Compare.moments_RT
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:31.996791+00:00
-- url     : https://prove2.me/theorems/6f53900b-4a78-4778-b5db-97639384d374
-- title:
--   §5.1, p. 26 — $E_{z,t}[R_T]=H(z,t)$ and $E_{z,t}[R_T^2]=H(z,t)$
-- statement:
--   Assume the standing market assumptions, the Conditions of Proposition 1, a solution $G$ of (20), initial data $t<T$, $z$ with factor path $Z=Z^{z,t}$, and let $R$ solve (38) from $R_t=1$. With $H=-1/G$,
--   $$\mathbb E_{z,t}[R_T]=H(z,t),\qquad \mathbb E_{z,t}[R_T^2]=H(z,t).$$
--   These two identities give the key identity (40), $(1-\mathbb E[R_T])/\mathrm{Var}[R_T]=-G(z,t)$, behind the coincidence of the MMV and MV strategies. They also yield the mean and variance of the optimal wealth.
--
--   **Formalization Note** The display is in the proof of Theorem 8 and precedes every use of Assumption 1, so Assumption 1 is not a hypothesis. The expectations are Bochner integrals under $\mathbb P$; the moments are finite for the solution of the linear SDE (38).
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 26, §5.1, proof of Theorem 8 (unnumbered display)

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- §5.1, proof of Theorem 8 (p. 26): the solution `R` of (38) has
`E_{z,t}[R_T] = H(z, t)` and `E_{z,t}[R_T²] = H(z, t)`, where `H = −1/G`. -/
theorem moments_RT {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (hP1 : PropOneConditions M) (G : ℝ → ℝ → ℝ) (hG : IsGSolution M G)
    (t : ℝ≥0) (ht : t < M.T) (z : ℝ) (Z : ℝ≥0 → Ω → ℝ) (hZ : M.IsFactor t z Z)
    (R : ℝ≥0 → Ω → ℝ) (hR : IsRProcess M G t Z R) :
    ∫ ω, R M.T ω ∂M.P = Hf G z t ∧ ∫ ω, R M.T ω ^ 2 ∂M.P = Hf G z t := by sorry

end MonotoneMVJump.Compare
