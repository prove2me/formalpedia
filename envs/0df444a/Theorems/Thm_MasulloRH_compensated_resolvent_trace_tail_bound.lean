-- Prove2me | Theorems.Thm_MasulloRH_compensated_resolvent_trace_tail_bound
-- name    : MasulloRH.compensated_resolvent_trace_tail_bound
-- status  : Open
-- author  : @ibecca
-- created : 2026-11-22T00:06:43.202039+00:00
-- url     : https://prove2.me/theorems/8a20c4f3-820d-421c-963a-8cd7290bb154
-- title:
--   Analytic tail certificate for the compensated regularized trace
-- statement:
--   Fix $0<\alpha<1/2$. The regularized trace at $s=3$ has a full-strip reference value and a narrower-window value. This theorem isolates the remaining analytic obligation in the compensated shifted-resolvent strategy: assuming the explicit high-height kernel certificate is available for every $0\le\beta\le1$ and $\gamma^2\ge36$, prove that the narrow-window defect is nonnegative,
--
--   $$
--   0\le \operatorname{Re}\bigl(\mathrm{RHS}_{\alpha}(3)-\mathrm{RHS}_{1/2}(3)\bigr).
--   $$
--
--   The intended proof must supply the finite low-height bookkeeping, the absolutely convergent high-height summation, and the passage from the compensated resolvent to the totalized regularized spectral sum. This node is deliberately an open analytic certificate: it does not assume the Riemann hypothesis, does not invoke any generic RH theorem, and does not claim that the local arithmetic estimate alone controls the trace tail.
-- source:
--   Masullo, The Music of the Primes, §§1.4.2–1.4.5 and Theorem 12.5.1.1 (20 November 2026 draft), with the compensated-resolvent/tail-certificate strategy recorded in the Prove2Me Masullo mission discussion, comment ad8fb92e-0c03-4bee-937c-638f829135a3.

import Definitions.Def_MasulloRH_RegularizedTrace
open MasulloRH

theorem MasulloRH.compensated_resolvent_trace_tail_bound
    (α : ℝ) (hα : 0 < α) (hsmall : α < 1 / 2)
    (hkernel :
      ∀ (β γ T : ℝ), 0 ≤ β → β ≤ 1 → 36 ≤ γ ^ 2 →
        let a := 3 - β
        let b := 5 / 2 - β
        let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
        let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
        0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k) :
    0 ≤ (regularizedTraceRHS α 3).re - (regularizedTraceRHS (1 / 2) 3).re := by sorry
