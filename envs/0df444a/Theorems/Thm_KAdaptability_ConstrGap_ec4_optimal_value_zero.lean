-- Prove2me | Theorems.Thm_KAdaptability_ConstrGap_ec4_optimal_value_zero
-- name    : KAdaptability.ConstrGap.ec4_optimal_value_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:01:51.792139+00:00
-- url     : https://prove2.me/theorems/ed8388bf-35d2-4319-9878-a18fa842854e
-- title:
--   Proof of Theorem 4, (EC.4) — the instance (EC.4) of 𝒫 has optimal value 0
-- statement:
--   Let $Q\in\mathbb N$ and consider the instance (EC.4) of the two-stage robust binary program $\mathcal P$: no first-stage decision, $\mathcal Y=\{0,1\}^Q$, zero objective, second-stage constraints $y_q-\xi_q\le\frac12$ and $\xi_q-y_q\le\frac12$ ($q=1,\dots,Q$), and uncertainty set $[0,1]^Q$ (augmented by $\xi_{Q+1}=1$ to make the right-hand side linear). Then
--   $$\operatorname{opt}(\text{EC.4})=\sup_{\xi\in[0,1]^Q}\ \inf_{y\in\{0,1\}^Q}\{0 : y_q-\xi_q\le\tfrac12,\ \xi_q-y_q\le\tfrac12,\ q=1,\dots,Q\}=0.$$
--
--   In words: for every realization of the parameter some binary recourse decision is feasible, so the fully adaptive problem $\mathcal P$ attains the value $0$ of its objective. This is the first half of the proof of Theorem 4.
--
--   **Formalization Note** The value is the general optimal value $\operatorname{opt}(\mathcal P)$ of `KAdaptability.ConstrGap.Values` evaluated at the instance `inst Q`, computed in `EReal`; an infeasible second stage would contribute $+\infty$.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec5 (PDF p. 39), Proof of Theorem 4, (EC.4)

import Mathlib
import Definitions.Def_KAdaptability_ConstrGap_Problem
import Definitions.Def_KAdaptability_ConstrGap_Values
import Definitions.Def_KAdaptability_ConstrGap_Instance

open Matrix

namespace KAdaptability.ConstrGap

/-- Proof of Theorem 4, p. ec5: the two-stage robust binary program (EC.4) — the instance
`inst nQ` of 𝒫 — has optimal value `0`. -/
theorem ec4_optimal_value_zero (nQ : ℕ) : (inst nQ).optP = 0 := by sorry

end KAdaptability.ConstrGap
