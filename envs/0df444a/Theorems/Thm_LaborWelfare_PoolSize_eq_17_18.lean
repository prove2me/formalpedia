-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_eq_17_18
-- name    : LaborWelfare.PoolSize.eq_17_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:27.590664+00:00
-- url     : https://prove2.me/theorems/8a66616c-af51-42da-b4db-3d54e3b46652
-- title:
--   (17)–(18), p. OA7 — first-order conditions L(D*, S*) = 0 and ∂Π/∂S = 0 at the optimum
-- statement:
--   In the base model ($h>0$) with $N>\underline N$, every optimal outcome $(p^*,w^*,D^*,S^*)$ satisfies the first-order conditions
--   $$L(D^*,S^*)=0,\qquad \frac{h\,(D^*/S^*)^{\beta+1}\big((\beta+1)S^*-\beta D^*\big)}{(S^*-D^*)^2}-\frac{4S^*}{NE[1/a]}=0,$$
--   where $L(D,S)=\bar v-2\bar vD/\Lambda-h(D/S)^\beta((\beta+1)S-\beta D)/(S-D)^2$ is $\partial\Pi/\partial D$.
--
--   These two equations characterize the interior optimum and drive the proofs of Lemma 13 and of every part of Theorem 2.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), displays (17)–(18), proof of Theorem 2, Part (iv), p. OA7 (also used in the proof of Lemma 13, p. OA4)

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- (17)–(18), p. OA7: the first-order conditions at the optimum. -/
theorem eq_17_18 (M : Model) (hM : M.Std) (hh : 0 < M.h) (N : ℝ) (hN : Nlow M < N) (o : Outcome)
    (ho : IsOptimal M N o) :
    Lfoc M o.D o.S = 0 ∧
      M.h * (o.D / o.S) ^ (M.beta + 1) * ((M.beta + 1) * o.S - M.beta * o.D) / (o.S - o.D) ^ 2 -
        4 * o.S / (N * Einv M) = 0 := by sorry

end LaborWelfare.PoolSize
