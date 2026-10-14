-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_theorem_9
-- name    : MonotoneMVJump.Compare.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:13.065512+00:00
-- url     : https://prove2.me/theorems/8863249c-0fbf-4c0d-ab9a-0bb5265f51fa
-- title:
--   Theorem 9 — the optimal MMV and MV utilities coincide iff Assumption 1 holds (over $\mathcal Q^t$ and over $\mathcal Q_0$)
-- statement:
--   Assume the standing market assumptions, the Conditions of Proposition 1, a solution $G$ of (20), and initial data $t<T$, $z$ with factor path $Z=Z^{z,t}$. Let $\theta>0$ and $x\in\mathbb R$. Write
--   1. $U^*=\sup_{\pi\in\mathcal B_{x,z,t}}U_\theta(X^\pi_T)$ for the optimal MV utility;
--   2. $V^*=\sup_{\pi\in\mathcal A_{x,1/(2\theta),z,t}}V_\theta(X^\pi_T)$ for the optimal MMV utility over the Doléans-Dade measures $\mathcal Q^t$;
--   3. $V^{0,*}=\sup_{\pi\in\mathcal A_{x,1/(2\theta),z,t}}V^0_\theta(X^\pi_T)$ for the optimal MMV utility over $\mathcal Q_0$.
--
--   Then
--   $$U^*=V^*\iff\text{Assumption 1 holds at }(z,t),\qquad\text{and}\qquad U^*=V^{0,*}\iff\text{Assumption 1 holds at }(z,t).$$
--
--   So in a jump-diffusion market, mean-variance and monotone mean-variance investors attain the same optimal utility exactly under Assumption 1. This holds whether the MMV investor's set of robust measures is $\mathcal Q^t$ or all of $\mathcal Q_0$.
--
--   **Formalization Note** The three optimal utilities are suprema in the extended reals over the full admissible classes of Definitions 2 and 3. They are not the closed forms of Theorems 4 and 7. The MMV problem is taken at $y=1/(2\theta)$ (Remark 2). $G$ is a hypothesis in the bounded class of `MonotoneMVJump.Compare.PDE`, in place of Proposition 1.
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 28, Theorem 9

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- Theorem 9 (p. 28): from the initial data `(x, z, t)`, the optimal MV utility
`sup_{π ∈ ℬ} U_θ(X^π_T)` equals the optimal MMV utility `sup_{π ∈ 𝒜} V_θ(X^π_T)` if and only if
Assumption 1 holds at `(z, t)`, both when `V_θ` minimizes over the Doléans-Dade measures `𝒬^t`
and when it minimizes over `𝒬₀`. -/
theorem theorem_9 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (hP1 : PropOneConditions M) (G : ℝ → ℝ → ℝ) (hG : IsGSolution M G)
    (t : ℝ≥0) (ht : t < M.T) (z : ℝ) (Z : ℝ≥0 → Ω → ℝ) (hZ : M.IsFactor t z Z)
    (θ : ℝ) (hθ : 0 < θ) (x : ℝ) :
    (M.mvValue t θ x Z = M.mmvValueQt t θ x Z ↔ Assumption1 M G t Z) ∧
      (M.mvValue t θ x Z = M.mmvValueQ0 t θ x Z ↔ Assumption1 M G t Z) := by sorry

end MonotoneMVJump.Compare
