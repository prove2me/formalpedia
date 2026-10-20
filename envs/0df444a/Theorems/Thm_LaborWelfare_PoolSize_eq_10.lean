-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_eq_10
-- name    : LaborWelfare.PoolSize.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:54.870306+00:00
-- url     : https://prove2.me/theorems/0ea88b63-f82e-44ef-8efc-db9a60e0ddd5
-- title:
--   (10), p. OA1 — LW = (NE[1/a]/4)(wD/S)² = S²/(NE[1/a])
-- statement:
--   Let $h\ge0$, $N>0$, and let $(p,w,D,S)$ with $w\ge 0$ be such that $(D,S)$ is a market equilibrium at $(p,w)$. Then total labor welfare has the closed forms
--   $$LW=N\int\Big[\frac{wD}{S}x^*(a)-a\,x^*(a)^2\Big]dF(a)=\frac{NE[1/a]}{4}\Big(\frac{wD}{S}\Big)^2=\frac{S^2}{NE[1/a]}.$$
--
--   In particular average labor welfare is $E[1/a]\,w_e^2/4$, a strictly increasing function of the effective wage $w_e=wD/S$.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), display (10), p. OA1

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- (10), p. OA1: `LW = (N E[1/a]/4)(wD/S)² = S²/(N E[1/a])` at any market equilibrium with `w ≥ 0`. -/
theorem eq_10 (M : Model) (hM : M.Std) (N : ℝ) (hN : 0 < N) (o : Outcome) (hw : 0 ≤ o.w)
    (ho : IsMarketEq M N o.p o.w o.D o.S) :
    laborWelfare M N o = N * Einv M / 4 * effWage o ^ 2 ∧
      laborWelfare M N o = o.S ^ 2 / (N * Einv M) := by sorry

end LaborWelfare.PoolSize
