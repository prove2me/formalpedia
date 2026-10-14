-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_theorem_6
-- name    : MonotoneMVJump.Compare.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:24.519825+00:00
-- url     : https://prove2.me/theorems/747a608e-a1e6-4725-98bf-a6e8b7e24ae9
-- title:
--   Theorem 6 — the feedback (37) is optimal for Problem 3 and $U_D(x,z,t)=-(x-D)^2/G(z,t)$
-- statement:
--   Assume the standing market assumptions, the Conditions of Proposition 1, a solution $G$ of (20), initial data $t<T$, $z$ with factor path $Z=Z^{z,t}$, and $x,D\in\mathbb R$. Then:
--   1. there is an admissible pair $(\pi^*(D),X^{\pi^*(D)})$, $\pi^*(D)\in\mathcal B_{x,z,t}$, following the feedback (37) on $[t,T]$:
--   $$\pi^*(D)(s)=-\frac{X^{\pi^*(D)}_{s-}-D}{\Sigma(Z_s)}\Big[\mu(Z_s)-r-\sigma(Z_s)b(Z_s)\rho_W\frac{G_z(Z_s,s)}{G(Z_s,s)}\Big];$$
--   2. every such pair has $\mathbb E[(X^{\pi^*(D)}_T-D)^2]=-(x-D)^2/G(z,t)$;
--   3. the value of Problem 3 is $U_D(x,z,t)=\inf_{\pi\in\mathcal B}\mathbb E[(X^\pi_T-D)^2]=-(x-D)^2/G(z,t)$.
--
--   This is the quadratic-target auxiliary problem that the Lagrangian embedding of the MV problem reduces to.
--
--   **Formalization Note** (37) is printed with $G_z(Z_s,t)/G(Z_s,t)$. Every other occurrence of this control (p. 22, (39), the proof of Theorem 8) evaluates at $(Z_s,s)$, so it is formalized at $(Z_s,s)$.
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 22, Theorem 6, (37)

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- Theorem 6 (p. 22): for every target `D`, a feedback pair of (37) exists in `ℬ_{x,z,t}`, every
such pair attains `J_D = −(x − D)²/G(z, t)`, and the value of Problem 3 is
`U_D(x, z, t) = −(x − D)²/G(z, t)`. -/
theorem theorem_6 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (hP1 : PropOneConditions M) (G : ℝ → ℝ → ℝ) (hG : IsGSolution M G)
    (t : ℝ≥0) (ht : t < M.T) (z : ℝ) (Z : ℝ≥0 → Ω → ℝ) (hZ : M.IsFactor t z Z)
    (x D : ℝ) :
    (∃ π X : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T → π s ω = problem3Strategy M G D Z X s ω) ∧
          M.AdmB t x Z π X) ∧
      (∀ π X : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T → π s ω = problem3Strategy M G D Z X s ω) →
          M.AdmB t x Z π X → M.JD D X = -(x - D) ^ 2 / G z t) ∧
      M.problem3Value t x D Z = ((-(x - D) ^ 2 / G z t : ℝ) : EReal) := by sorry

end MonotoneMVJump.Compare
