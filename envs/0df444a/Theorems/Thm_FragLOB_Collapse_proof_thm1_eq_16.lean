-- Prove2me | Theorems.Thm_FragLOB_Collapse_proof_thm1_eq_16
-- name    : FragLOB.Collapse.proof_thm1_eq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:53.569435+00:00
-- url     : https://prove2.me/theorems/14357e02-0cef-45da-9e18-d79368cf1ee3
-- title:
--   Proof of Theorem 1, (16), p. 1332 — the lifting map (15) preserves the workload, so the delays are W*/(μβ_i)
-- statement:
--   Let $\pi^*$ be a routing decision and $W^* > 0$ a workload, and suppose the aggregate balance (14) holds:
--   $\sum_{i=1}^N \big(\lambda_i + \Lambda\int_0^\infty \pi^*_i(\gamma)\,dF(\gamma)\big) = \mu$, where $F$ is the probability distribution of investor types on $[0,\infty)$. Define $Q^*$ by the lifting map (15),
--   $Q^*_i = \big(\lambda_i + \Lambda\int_0^\infty \pi^*_i\,dF\big)\,W^*/(\mu\beta_i)$. Then the workload of $Q^*$ is $W^*$ and every exchange's expected delay under $Q^*$ is $W^*/(\mu\beta_i)$:
--
--   $$\beta^\top Q^* = W^*, \qquad \frac{W^*}{\mu\beta_i} = \frac{\beta^\top Q^*}{\mu\beta_i} = \frac{Q^*_i}{\mu_i(Q^*)} \quad (i = 1,\dots,N).$$
--
--   This is the computation opening the proof of Theorem 1: the delays faced in the lifted state are exactly those the aggregated problem (13) charges.
--
--   **Formalization Note.** At an exchange with $Q^*_i = 0$ the delay is the convention $W/(\mu\beta_i)$ of the model file, so the second claim reads $W^*/(\mu\beta_i)$ there as well. The hypothesis $W^* > 0$ is needed: at $W^* = 0$ the lifted state is $Q^* = 0$, whose workload is $0$ and at which (4) is undefined.
-- source:
--   Maglaras, Moallemi & Zheng, Operations Research 69(4):1324–1348 (2021), p. 1332, proof of Theorem 1, display before (16) and eq. (16)

import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

namespace FragLOB.Collapse

theorem proof_thm1_eq_16 {N : ℕ} (M : Market N) (hM : M.Standing) (F : Measure ℝ)
    [IsProbabilityMeasure F] (hF : F (Set.Iio 0) = 0) (pi : ℝ → Fin (N + 1) → ℝ)
    (hpi : IsRouting pi) (hbal : AggBalance M F pi) (W : ℝ) (hW : 0 < W) :
    workload M (lift M F pi W) = W ∧
      ∀ i, delay M (lift M F pi W) i = W / (M.mu * M.beta i) := by sorry

end FragLOB.Collapse
