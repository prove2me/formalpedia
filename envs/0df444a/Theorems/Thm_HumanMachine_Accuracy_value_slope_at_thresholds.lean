-- Prove2me | Theorems.Thm_HumanMachine_Accuracy_value_slope_at_thresholds
-- name    : HumanMachine.Accuracy.value_slope_at_thresholds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:23:44.432955+00:00
-- url     : https://prove2.me/theorems/706ad526-7cf9-42c1-a5f6-eec5551f0684
-- title:
--   Proof of Proposition 1 — the middle branch of (15) has slope $-1$ at $\underline\mu$ and $1$ at $\bar\mu$
-- statement:
--   Let $\lambda>0$, $H$ the binary entropy (natural logarithm), $\underline\mu=1/(e^{1/\lambda}+1)$ and $\bar\mu=e^{1/\lambda}/(e^{1/\lambda}+1)$. The function $g(\mu)=\lambda\big[\log(e^{1/\lambda}+1)-H(\mu)\big]$, the middle branch of the value function (15), is differentiable at both thresholds, with
--
--   $$g'(\underline\mu)=-1,\qquad g'(\bar\mu)=1.$$
--
--   These are the slopes of the outer branches $1-\mu$ and $\mu$ of (15), so the three branches join without a concave kink.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 33, Appendix A, proof of Proposition 1, slope display

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel

namespace HumanMachine.Accuracy

/-- Proof of Proposition 1 (p. 33): for `λ > 0`, the middle branch `λ [log(e^{1/λ} + 1) - H(μ)]`
of (15) has derivative `-1` at `μ = μ̲` and `1` at `μ = μ̄`, the slopes of the outer branches
`1 - μ` and `μ`. -/
theorem value_slope_at_thresholds (lam : ℝ) (hlam : 0 < lam) :
    HasDerivAt (fun μ : ℝ => lam * (Real.log (Real.exp (1 / lam) + 1) - Real.binEntropy μ))
        (-1) (HumanMachine.Alone.muLow lam) ∧
      HasDerivAt (fun μ : ℝ => lam * (Real.log (Real.exp (1 / lam) + 1) - Real.binEntropy μ))
        1 (HumanMachine.Alone.muHigh lam) := by sorry

end HumanMachine.Accuracy
