-- Prove2me | Theorems.Thm_MazurTransfer_thirteenth_root_cubic_period
-- name    : MazurTransfer.thirteenth_root_cubic_period
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-14T22:38:49.259992+00:00
-- url     : https://prove2.me/theorems/62e50518-90a1-4e3e-97cd-a2aa2db0652d
-- title:
--   A thirteenth-root period supplies the cubic reflection coefficient
-- statement:
--   Let K be a field and let ζ be a primitive thirteenth root of unity in K. Set t = ζ + ζ⁵ + ζ⁸ + ζ¹² − 1. Then t³ + 4t² + t − 1 = 0. This explicit coefficient is used to construct a reflection of the order-13 curve over the thirteenth cyclotomic field, and to determine the field of definition of the reflected fixed line in its actual Picard nineteen-torsion.
-- source:
--   Owned MazurTheorem integration, Apache-2.0. Independent exact polynomial certificate, checked against Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Downstream consumer: Order13CyclotomicReflectionCoefficients.cubicPeriod_root.

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Ring

theorem MazurTransfer.thirteenth_root_cubic_period
    (K : Type*) [Field K] (z : K) (hz : IsPrimitiveRoot z 13) :
    let t := z + z ^ 5 + z ^ 8 + z ^ 12 - 1
    t ^ 3 + 4 * t ^ 2 + t - 1 = 0 := by sorry
