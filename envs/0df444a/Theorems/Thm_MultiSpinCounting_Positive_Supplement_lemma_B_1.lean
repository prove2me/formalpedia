-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_Supplement_lemma_B_1
-- name    : MultiSpinCounting.Positive.Supplement.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:29:33.003796+00:00
-- url     : https://prove2.me/theorems/08a5c0f0-c0cc-4cbf-a1aa-3415368774ff
-- title:
--   Lemma B.1 (used in the proof of Theorem 1.7) — uniform parameter choice
-- statement:
--   For every $\eta\in(0,1)$ there exists a real threshold $d_0(\eta)\ge8$, chosen before $d$ and $q$, such that for every real $d\ge d_0$ and every integer $q\ge(2+\eta)d$, the parameters (5.10), (5.12), (5.16) satisfy all of
--   $$D-3>(1+\delta)d,\quad D<q-1,$$
--   $$d(\gamma+\sqrt r)\le\lambda_0<\rho<1,\qquad edr^{1/4}\le\tfrac14,\qquad ey\le\tfrac14.$$
--   Here $D=\lfloor(d+q)/3\rfloor$, $\gamma=(q-D-1)^{-1}$, $\delta=(q/d-2)/6$, $r=e^{-dh(\delta)}$, $h(x)=(1+x)\log(1+x)-x$, $\lambda_0=(3+\eta/2)/(3+\eta)$, $\rho=(1+\lambda_0)/2$, $y=4dq^{200}e^{-((q-1)\log2-d)/2}$. The common threshold is uniform over $q$ and supplies every probabilistic estimate in §5.
--
--   Differences from the source:
--   - encoding: the four numbered parameter estimates → their explicit conjunction with integer floor D and real arithmetic; reason: all inequalities and constants are unchanged
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 35, Lemma B.1

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Supplement_Parameters

namespace MultiSpinCounting.Positive.Supplement

/-- Lemma B.1, p. 35, all four estimates with a common q-independent threshold. -/
theorem lemma_B_1 (η : ℝ) (hη : 0 < η ∧ η < 1) :
    ∃ d0 : ℝ, 8 ≤ d0 ∧ ∀ d : ℝ, d0 ≤ d → ∀ q : ℕ,
      (2 + η) * d ≤ (q : ℝ) →
      ParameterEstimates η d q ∧ Real.exp 1 * y5 d q ≤ 1 / 4 := by sorry

end MultiSpinCounting.Positive.Supplement
