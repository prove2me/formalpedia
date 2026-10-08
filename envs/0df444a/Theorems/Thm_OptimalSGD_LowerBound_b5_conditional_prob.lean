-- Prove2me | Theorems.Thm_OptimalSGD_LowerBound_b5_conditional_prob
-- name    : OptimalSGD.LowerBound.b5_conditional_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:20.492319+00:00
-- url     : https://prove2.me/theorems/93a15d10-9877-4b37-afb9-e9a3060449a7
-- title:
--   App. B.5, p. 17 — Pr(w_{t,1} ∉ [0, c/t] | w_{t−1,1} ≥ 0) ≥ 3/4 when c/t < 1
-- statement:
--   Consider SGD on Example B (domain $W=[-1,1]^d$, the state-dependent oracle $\hat g_t=w_t+(Z_t,0,\dots,0)$ if $w_{t,1}\ge0$ and $w_t+(-7,0,\dots,0)$ otherwise, with $Z_1,Z_2,\dots$ independent and uniform on $[-1,3]$), run with step sizes $\eta_t=c/t$, $c>0$, from a starting point $w_1\in W$ with $w_{1,1}\ge0$. Let $t\ge2$ be an integer with $c/t<1$. Then
--   $$\Pr\big(w_{t,1}\notin[0,c/t]\ \big|\ w_{t-1,1}\ge0\big)\ \ge\ \frac34 .$$
--   It is stated in the equivalent multiplicative form
--   $$\Pr\big(w_{t,1}\notin[0,c/t]\ \text{and}\ w_{t-1,1}\ge0\big)\ \ge\ \frac34\,\Pr\big(w_{t-1,1}\ge0\big),$$
--   which is the conditional inequality whenever $\Pr(w_{t-1,1}\ge0)>0$ and holds trivially otherwise.
--
--   In the proof of Theorem 4 this bound says that, after a round with nonnegative first coordinate, the next iterate avoids the narrow interval $[0,c/t]$ with probability at least $3/4$.
--
--   **Formalization Note** The probability is the product law $\mathrm{Unif}[-1,3]^{\otimes T}$ of a noise sequence of any horizon $T\ge t$ (the event only involves $Z_1,\dots,Z_{t-1}$). The paper's $w_t$ is the Lean run at index $t-1$. In the paper's derivation the step from $w_{t-1}$ to $w_t$ is written with $c/t$ and $Z_t$; by the definition of SGD it uses $\eta_{t-1}=c/(t-1)$ and $Z_{t-1}$, which is what the Lean run does. The stated bound is the paper's.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 17, App. B.5 (proof of Theorem 4), display Pr(w_{t,1} ∉ [0, c/t] | w_{t−1,1} ≥ 0) ≥ 3/4

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_UnderstandingML_Linear
import Definitions.Def_OptimalSGD_LowerBound_Model

namespace OptimalSGD.LowerBound

open MeasureTheory UnderstandingML

/-- **App. B.5, p. 17** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7): for SGD on Example B
with `η_t = c/t` and `c/t < 1`, `Pr(w_{t,1} ∉ [0, c/t] | w_{t−1,1} ≥ 0) ≥ 3/4`, stated in the
multiplicative form `Pr(w_{t,1} ∉ [0, c/t] ∧ w_{t−1,1} ≥ 0) ≥ (3/4) Pr(w_{t−1,1} ≥ 0)`, which is
the conditional statement when `Pr(w_{t−1,1} ≥ 0) > 0` and is trivial otherwise. The paper's
`w_t` is `runB … (t − 1)`; the noise is i.i.d. uniform on `[−1, 3]` over a horizon `T ≥ t`. -/
theorem b5_conditional_prob (d : ℕ) [NeZero d] (c : ℝ) (hc : 0 < c) (w₁ : Vec d)
    (hw₁ : w₁ ∈ box (-1) 1) (hw₁₁ : 0 ≤ w₁ 0) (t T : ℕ) (ht : 2 ≤ t) (hct : c < (t : ℝ))
    (hT : t ≤ T) :
    (3 / 4 : ENNReal) * iidLaw noiseLaw T {Z | 0 ≤ runB c w₁ (extendNoise Z) (t - 2) 0}
      ≤ iidLaw noiseLaw T
          {Z | runB c w₁ (extendNoise Z) (t - 1) 0 ∉ Set.Icc 0 (c / (t : ℝ)) ∧
            0 ≤ runB c w₁ (extendNoise Z) (t - 2) 0} := by sorry

end OptimalSGD.LowerBound
