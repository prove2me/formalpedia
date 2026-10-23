-- Prove2me | Theorems.Thm_FragLOB_Collapse_proof_thm1_flow_balance
-- name    : FragLOB.Collapse.proof_thm1_flow_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:46.053363+00:00
-- url     : https://prove2.me/theorems/27cd3576-8f1b-4e45-b34c-cdd546d722f4
-- title:
--   Proof of Theorem 1, rewriting (15), p. 1332 — the lifting map satisfies the flow balance (11)
-- statement:
--   Let $\pi^*$ be a routing decision and $W^* > 0$, and suppose the aggregate balance (14) holds. Let $Q^*$ be given by the lifting map (15), $Q^*_i = \big(\lambda_i + \Lambda\int_0^\infty \pi^*_i\,dF\big)\,W^*/(\mu\beta_i)$. Then for every exchange $i$,
--
--   $$\lambda_i + \Lambda\int_0^\infty \pi^*_i(\gamma)\,dF(\gamma) = \mu\frac{\beta_i Q^*_i}{W^*} = \mu\frac{\beta_i Q^*_i}{\beta^\top Q^*} = \mu_i(Q^*),$$
--
--   which is the flow balance condition (11) of Definition 1.
--
--   This is the second half of the forward direction of Theorem 1: the lifted queue lengths balance the arriving limit orders against the market orders the attraction model sends to each exchange.
--
--   **Formalization Note.** $F$ is a probability distribution on $[0,\infty)$; $W^* > 0$ is needed because at $W^* = 0$ the lifted state is $0$ and $\mu_i(0)$ is undefined.
-- source:
--   Maglaras, Moallemi & Zheng, Operations Research 69(4):1324–1348 (2021), p. 1332, proof of Theorem 1 ("rewriting (15)"), eq. (11)

import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

namespace FragLOB.Collapse

theorem proof_thm1_flow_balance {N : ℕ} (M : Market N) (hM : M.Standing) (F : Measure ℝ)
    [IsProbabilityMeasure F] (hF : F (Set.Iio 0) = 0) (pi : ℝ → Fin (N + 1) → ℝ)
    (hpi : IsRouting pi) (hbal : AggBalance M F pi) (W : ℝ) (hW : 0 < W) :
    ∀ i, M.lam i + M.Lam * ∫ γ, pi γ i.succ ∂F = marketRate M (lift M F pi W) i := by sorry

end FragLOB.Collapse
