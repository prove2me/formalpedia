-- Prove2me | Theorems.Thm_LogSobolevMC_TwoPoint_theorem_A_2
-- name    : LogSobolevMC.TwoPoint.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:44.198562+00:00
-- url     : https://prove2.me/theorems/3742aae3-f48f-479e-8555-36307318f48a
-- title:
--   Theorem A.2, p. 743 — the two-point chain (θ, 1 − θ) has α(θ) = (1 − 2θ)/log[(1 − θ)/θ], and 1/2 at θ = 1/2
-- statement:
--   Let $0<\theta\le1/2$ and consider the Markov chain on $\{0,1\}$ with matrix
--
--   $$\begin{pmatrix}\theta&1-\theta\\ \theta&1-\theta\end{pmatrix}.$$
--
--   It has invariant measure $\pi(0)=\theta$, $\pi(1)=1-\theta$, and its log-Sobolev constant is
--
--   $$\alpha(\theta)=\frac{1-2\theta}{\log[(1-\theta)/\theta]}\quad(\theta<1/2),\qquad \alpha(1/2)=\frac12,$$
--
--   the value at $\theta=1/2$ being the limit of the formula, as the theorem prescribes.
--
--   Theorem A.2 is the two-point case to which the proof of Theorem A.1 reduces the general chain $K(x,y)=\pi(y)$.
--
--   **Formalization Note** At $\theta=1/2$ the printed quotient is $0/0$, which Lean would evaluate to $0$; the statement gives the limit value $1/2$ explicitly, as the page instructs.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 743, Theorem A.2

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing

/-- Theorem A.2 (p. 743): the chain on `{0, 1}` with both rows `(θ, 1 − θ)`, `0 < θ ≤ 1/2`, has
invariant measure `π = (θ, 1 − θ)` and log-Sobolev constant `(1 − 2θ)/log[(1 − θ)/θ]`, replaced by its
limit value `1/2` at `θ = 1/2`. -/
theorem theorem_A_2 (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1 / 2) :
    IsStationary (twoPointChain θ) (twoPointPi θ) ∧
      LogSobolevMC.ChiSquare.logSobolev (twoPointChain θ) (twoPointPi θ) =
        if θ = 1 / 2 then 1 / 2 else (1 - 2 * θ) / Real.log ((1 - θ) / θ) := by sorry

end LogSobolevMC.TwoPoint
