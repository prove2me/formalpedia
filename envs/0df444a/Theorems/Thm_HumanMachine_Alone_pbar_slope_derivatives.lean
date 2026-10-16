-- Prove2me | Theorems.Thm_HumanMachine_Alone_pbar_slope_derivatives
-- name    : HumanMachine.Alone.pbar_slope_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:11.307127+00:00
-- url     : https://prove2.me/theorems/1d19099e-a17e-4eec-99c6-eaf5c273ecb5
-- title:
--   Appendix A — interior slope and prior-threshold derivatives
-- statement:
--   For every $\lambda>0$, the interior expression $\bar p$ is affine in the prior $\mu$ with a positive slope. Its slope and intercept are
--
--   $$
--   s(\lambda)=\frac{1}{1-e^{-1/\lambda}}+\frac{1}{e^{1/\lambda}-1}>0,\qquad
--   \bar p(\lambda,\mu)=s(\lambda)\mu-\frac{1}{e^{1/\lambda}-1}.
--   $$
--
--   The threshold derivatives are $\overline\mu'(\lambda)=-e^{1/\lambda}/[\lambda^2(e^{1/\lambda}+1)^2]$ and $\underline\mu'(\lambda)=e^{1/\lambda}/[\lambda^2(e^{1/\lambda}+1)^2]$. These formulas supply the monotonicity clauses in Theorem 1.
--
--   **Formalization Note** Differentiability and signs are asserted only for positive $\lambda$, where all displayed denominators are nonzero.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 32 (PDF p. 33), proof of Theorem 1, final sentences and derivative displays.

import Mathlib
import Definitions.Def_HumanMachine_Alone_model

namespace HumanMachine.Alone

theorem pbar_slope_derivatives :
    (∀ lam : ℝ, 0 < lam →
      let slope := 1 / (1 - Real.exp (-(1 / lam))) +
        1 / (Real.exp (1 / lam) - 1)
      0 < slope ∧ ∀ mu : ℝ, pBar lam mu = slope * mu -
        1 / (Real.exp (1 / lam) - 1)) ∧
    (∀ lam : ℝ, 0 < lam →
      HasDerivAt muHigh
        (-(1 / lam ^ 2) * Real.exp (1 / lam) / (Real.exp (1 / lam) + 1) ^ 2) lam ∧
      HasDerivAt muLow
        ((1 / lam ^ 2) * Real.exp (1 / lam) / (Real.exp (1 / lam) + 1) ^ 2) lam) := by sorry

end HumanMachine.Alone
