-- Prove2me | Theorems.Thm_OnlineCombOpt_Exp2LB_appA_eta_optimization
-- name    : OnlineCombOpt.Exp2LB.appA_eta_optimization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:06.853747+00:00
-- url     : https://prove2.me/theorems/2796efc4-c42d-4d73-8974-70ab48b3f64f
-- title:
--   App. A, pp. 14–15 — max((nd/16) tanh(ηd/8), min(d log 2/(12η), nd/12)) ≥ min(0.04 nd, 0.01 d^{3/2}√n)
-- statement:
--   For all integers $n,d\ge 0$ and every learning rate $\eta>0$,
--   $$\max\Bigl(\frac{nd}{16}\tanh\Bigl(\frac{\eta d}{8}\Bigr),\ \min\Bigl(\frac{d\log 2}{12\eta},\ \frac{nd}{12}\Bigr)\Bigr)\;\ge\;\min\bigl(0.04\,nd,\ 0.01\,d^{3/2}\sqrt n\bigr).$$
--
--   This is the optimization over the learning rate in the proof of Theorem 1: whatever $\eta$ is, one of the two adversaries of App. A forces a regret of at least $\min(0.04\,nd,\,0.01\,d^{3/2}\sqrt n)$, which equals $0.01\,d^{3/2}\sqrt n$ when $n\ge d$.
--
--   **Formalization Note** The paper takes the minimum over $\eta\in[0,+\infty)$, reading $d\log 2/(12\eta)$ as $+\infty$ at $\eta=0$; here the chain is stated pointwise for each $\eta>0$, because Lean reads $d\log2/(12\cdot 0)$ as $0$. The constants $0.04$ and $0.01$ are the reals $4/100$ and $1/100$, and $d^{3/2}=d\sqrt d$.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, App. A, pp. 14–15, the displays "sup R_n ≥ max(…)" (p. 14) and "A = min_{η∈[0,+∞)} max(…) ≥ … ≥ min(0.04 nd, 0.01 d^{3/2}√n)" (p. 15)

import Mathlib
import Definitions.Def_OnlineCombOpt_Exp2LB_Setting

open Finset

namespace OnlineCombOpt.Exp2LB

/-- App. A, pp. 14–15 (Audibert, Bubeck, Lugosi, arXiv:1204.4710v2), the optimization over the
learning rate, pointwise in `η > 0`:
`max((nd/16) tanh(ηd/8), min(d log 2/(12η), nd/12)) ≥ min(0.04 nd, 0.01 d^{3/2} √n)`. -/
theorem appA_eta_optimization (n d : ℕ) (η : ℝ) (hη : 0 < η) :
    min ((4 : ℝ) / 100 * n * d) ((1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n) ≤
      max ((n : ℝ) * d / 16 * Real.tanh (η * d / 8))
        (min ((d : ℝ) * Real.log 2 / (12 * η)) ((n : ℝ) * d / 12)) := by sorry

end OnlineCombOpt.Exp2LB
