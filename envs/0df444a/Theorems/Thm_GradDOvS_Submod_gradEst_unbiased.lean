-- Prove2me | Theorems.Thm_GradDOvS_Submod_gradEst_unbiased
-- name    : GradDOvS.Submod.gradEst_unbiased
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:54.336131+00:00
-- url     : https://prove2.me/theorems/8340397b-a5f7-4966-adb2-ed7204bbd35f
-- title:
--   p. 18, after (4) — the subgradient estimator (4) is unbiased
-- statement:
--   Let the simulation oracle satisfy Assumption 1 (independent slots, outputs centred at $f$ and $\sigma^2$-sub-Gaussian). For a fixed point $x$, an iteration $t$ and a coordinate $j$, the estimator (4)
--   $$\hat g_{\alpha(i)} = F(S^{x,i},\xi^1_i) - F(S^{x,i-1},\xi^2_{i-1}), \qquad i = 1,\dots,d,$$
--   built with the canonical consistent permutation $\alpha$ of $x$, has integrable coordinates and
--   $$\mathbb E[\hat g_j] = g_j,$$
--   where $g$ is the vector (3) at $x$ for the same permutation.
--
--   Unbiasedness is the starting point of the stochastic subgradient analysis; truncation then trades a small bias for bounded steps.
--
--   **Formalization Note** The point $x$ is deterministic (in Algorithm 2 the slots of iteration $t$ are independent of $x^t$, which is how the statement is used). No condition on $x$ is needed.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 18, display after eq. (4)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- p. 18, after (4): at a fixed point `x`, every coordinate of the estimator (4) is integrable and
has mean `g_j`, the vector (3) for the canonical consistent permutation of `x`. -/
theorem gradEst_unbiased {Ω : Type*} [MeasurableSpace Ω] {d T n : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Finset (Fin d) → ℝ) (σ : NNReal)
    (Z : Slot d T n → Ω → Finset (Fin d) → ℝ) (hZ : IsSimOracle P f σ Z)
    (t : Fin T) (x : Fin d → ℝ) (j : Fin d) :
    Integrable (fun ω => gradEst Z t x ω j) P ∧
      ∫ ω, gradEst Z t x ω j ∂P = chainGrad f (canonPerm x) j := by sorry

end GradDOvS.Submod
