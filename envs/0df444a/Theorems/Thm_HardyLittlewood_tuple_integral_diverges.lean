-- Prove2me | Theorems.Thm_HardyLittlewood_tuple_integral_diverges
-- name    : HardyLittlewood.tuple_integral_diverges
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T21:46:14.881417+00:00
-- url     : https://prove2.me/theorems/e9bc7d49-dcba-4e30-ad39-3d8d05b586dd
-- title:
--   The logarithmic-integral model diverges
-- statement:
--   For every multiplicity k + 1, the model integral of the first Hardy–Littlewood conjecture grows without bound: the integral of 1/(log t)^(k+1) over [2, n] tends to +∞ as n → ∞. This is the divergence that makes the conjecture's conclusion an infinitude statement: a positive constant against a diverging model forces the count to grow.
-- source:
--   Hardy and Littlewood (1923), Acta Math. 44, the logarithmic-integral model of the prime k-tuple asymptotic

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

namespace HardyLittlewood

/-- The model integral of the first Hardy–Littlewood conjecture diverges: for
every multiplicity k + 1, the integral of 1 / (log t)^(k+1) over [2, n] grows
without bound as n → ∞. -/
theorem tuple_integral_diverges (k : ℕ) :
    Filter.Tendsto (fun n => ∫ t in (2:ℝ)..(n:ℝ), 1 / (Real.log t) ^ (k + 1))
      Filter.atTop Filter.atTop := by
  sorry

end HardyLittlewood
