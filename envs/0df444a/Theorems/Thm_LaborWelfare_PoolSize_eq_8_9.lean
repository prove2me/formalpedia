-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_eq_8_9
-- name    : LaborWelfare.PoolSize.eq_8_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:55.182119+00:00
-- url     : https://prove2.me/theorems/239ec920-a62c-46ab-b783-7c83ab4c7eb5
-- title:
--   (8)–(9), p. OA1 — price, wage and profit as functions of demand D and supply S
-- statement:
--   In the base model ($h>0$), let $N>0$ and let $(p,w,D,S)$ be a feasible outcome. Then the price, the wage and the platform's profit are determined by $(D,S)$:
--   $$p=p(D,S)=\bar v-\frac{\bar vD}{\Lambda}-\frac{h(D/S)^\beta}{S-D},\qquad w=\frac{2S^2}{DNE[1/a]},\qquad (p-w)D=\Pi(D,S)=p(D,S)\,D-\frac{2S^2}{NE[1/a]}.$$
--
--   This reduction turns the platform's problem over prices and wages into a problem over demand and supply, the form in which every later result is proved.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), displays (8)–(9) and the sentences after them, p. OA1

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- (8)–(9), p. OA1: on a feasible outcome of the base model, the price is `p(D, S)`, the wage is
`2S²/(D N E[1/a])`, and the profit is `Π(D, S)`. -/
theorem eq_8_9 (M : Model) (hM : M.Std) (hh : 0 < M.h) (N : ℝ) (hN : 0 < N) (o : Outcome)
    (ho : IsFeasible M N o) :
    o.p = priceDS M o.D o.S ∧ o.w = 2 * o.S ^ 2 / (o.D * N * Einv M) ∧
      profit o = PiDS M N o.D o.S := by sorry

end LaborWelfare.PoolSize
