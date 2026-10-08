-- Prove2me | Theorems.Thm_OptimalSGD_LowerBound_eq_9
-- name    : OptimalSGD.LowerBound.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:14.118808+00:00
-- url     : https://prove2.me/theorems/0559e2e8-f802-472c-ab9e-b6bb12243586
-- title:
--   Eq. (9) — first-coordinate recursion of SGD on Example B
-- statement:
--   Consider Example B: the domain $W=[-1,1]^d$, the objective $F(w)=\tfrac12\|w\|^2+w_1$ for $w_1\ge0$ and $\tfrac12\|w\|^2-7w_1$ for $w_1<0$, and the oracle that at $w_t$ returns $\hat g_t=w_t+(Z_t,0,\dots,0)$ if $w_{t,1}\ge0$ and $\hat g_t=w_t+(-7,0,\dots,0)$ if $w_{t,1}<0$. Run projected SGD $w_{t+1}=\Pi_W(w_t-\eta_t\hat g_t)$ with $\eta_t=c/t$ from any starting point, along any sequence of noise values $Z_1,Z_2,\dots$ Then for every $t\ge1$ the first coordinate satisfies
--   $$w_{t+1,1}=\Pi_{[-1,1]}\left(\Big(1-\frac ct\Big)w_{t,1}-\begin{cases}Z_t\,\frac ct & w_{t,1}\ge0\\[2pt] -\frac{7c}{t} & w_{t,1}<0\end{cases}\right),$$
--   where $\Pi_{[-1,1]}(x)=\max\{-1,\min\{1,x\}\}$.
--
--   This is the one-dimensional recursion on which the paper's proof of Theorem 4 runs: the other coordinates do not influence the first.
--
--   **Formalization Note** The statement holds for every noise sequence and every real $c$. Index $k$ of the Lean run is the paper's $w_{k+1}$, so the paper's $t$ is $k+1$ and the noise of round $t$ is `Z k`.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 16, App. B.5, Eq. (9)

import Mathlib
import Definitions.Def_UnderstandingML_Linear
import Definitions.Def_OptimalSGD_LowerBound_Model

namespace OptimalSGD.LowerBound

open UnderstandingML

/-- **Eq. (9)** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7, App. B.5, p. 16). For SGD on
Example B with `η_t = c/t`, along every noise sequence, the first coordinate obeys
`w_{t+1,1} = Π_{[−1,1]}((1 − c/t) w_{t,1} − (Z_t c/t if w_{t,1} ≥ 0, −7c/t if w_{t,1} < 0))`.
Here index `k` of `runB` is the paper's `w_{k+1}`, so the paper's `t` is `k + 1` and the noise of
round `t` is `Z k`; `Π_{[−1,1]}(x) = max (−1) (min 1 x)`. -/
theorem eq_9 (d : ℕ) [NeZero d] (c : ℝ) (w₁ : Vec d) (Z : ℕ → ℝ) (k : ℕ) :
    runB c w₁ Z (k + 1) 0 =
      max (-1) (min 1
        ((1 - c / ((k : ℝ) + 1)) * runB c w₁ Z k 0
          - (if 0 ≤ runB c w₁ Z k 0 then Z k * (c / ((k : ℝ) + 1))
              else -7 * c / ((k : ℝ) + 1)))) := by sorry

end OptimalSGD.LowerBound
