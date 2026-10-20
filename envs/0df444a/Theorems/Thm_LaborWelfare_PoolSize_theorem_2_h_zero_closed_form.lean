-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_theorem_2_h_zero_closed_form
-- name    : LaborWelfare.PoolSize.theorem_2_h_zero_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:58.51914+00:00
-- url     : https://prove2.me/theorems/1ddc4f8a-056f-4472-a125-064e65db3434
-- title:
--   Proof of Theorem 2, case h = 0, pp. OA4–OA5 — unique optimum with D* = S* = v̄/(2(v̄/Λ + 2/(NE[1/a]))) and w* = v̄Λ/(v̄NE[1/a] + 2Λ)
-- statement:
--   In the benchmark with delay-insensitive customers ($h=0$, capacity constraint $D\le S$) and labor pool size $N>0$, the platform's problem has exactly one optimal outcome, and every optimal outcome satisfies
--   $$D^*=S^*=\frac{\bar v}{2\big(\bar v/\Lambda+2/(NE[1/a])\big)},\qquad w^*=\frac{\bar v\Lambda}{\bar vNE[1/a]+2\Lambda}.$$
--
--   Labor supply equals demand, so the wage and the effective wage coincide; the closed form for $w^*$ is the source of the monotonicity of the benchmark in Theorem 2.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), §3, p. 10 (existence, uniqueness, labor supply equals demand) and proof of Theorem 2, case h = 0, pp. OA4–OA5

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Proof of Theorem 2, case `h = 0`, pp. OA4–OA5 (with p. 10): the optimum exists, is unique, has
`D* = S* = v̄/(2(v̄/Λ + 2/(N E[1/a])))` and `w* = v̄Λ/(v̄ N E[1/a] + 2Λ)`. -/
theorem theorem_2_h_zero_closed_form (M : Model) (hM : M.Std) (hh : M.h = 0) (N : ℝ) (hN : 0 < N) :
    (∃! o : Outcome, IsOptimal M N o) ∧
      ∀ o, IsOptimal M N o →
        o.D = o.S ∧ o.S = M.vbar / (2 * (M.vbar / M.Lam + 2 / (N * Einv M))) ∧
          o.w = M.vbar * M.Lam / (M.vbar * N * Einv M + 2 * M.Lam) := by sorry

end LaborWelfare.PoolSize
