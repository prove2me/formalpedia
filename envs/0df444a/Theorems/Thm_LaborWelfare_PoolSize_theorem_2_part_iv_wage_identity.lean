-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_theorem_2_part_iv_wage_identity
-- name    : LaborWelfare.PoolSize.theorem_2_part_iv_wage_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:09.000581+00:00
-- url     : https://prove2.me/theorems/254582db-224f-4bbb-9adb-5506496d09e6
-- title:
--   Proof of Theorem 2, Part (iv), p. OA7 — at the optimum w* = ½v̄ − v̄D*/Λ
-- statement:
--   In the base model ($h>0$) with $N>\underline N$, every optimal outcome $(p^*,w^*,D^*,S^*)$ satisfies
--   $$w^*=\frac{\bar v}{2}-\frac{\bar vD^*}{\Lambda}.$$
--
--   Since $D^*$ increases in $N$ (Lemma 13), this identity shows that the wage decreases in $N$.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), proof of Theorem 2, Part (iv), p. OA7, "It is straightforward to derive from (17)-(18) that w* = ½v̄ − v̄D*/Λ"

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Proof of Theorem 2, Part (iv), p. OA7: at the optimum, `w* = v̄/2 - v̄ D*/Λ`. -/
theorem theorem_2_part_iv_wage_identity (M : Model) (hM : M.Std) (hh : 0 < M.h) (N : ℝ)
    (hN : Nlow M < N) (o : Outcome) (ho : IsOptimal M N o) :
    o.w = M.vbar / 2 - M.vbar * o.D / M.Lam := by sorry

end LaborWelfare.PoolSize
