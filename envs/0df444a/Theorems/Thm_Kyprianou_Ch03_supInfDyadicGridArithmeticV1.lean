-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDyadicGridArithmeticV1
-- name    : Kyprianou.Ch03.supInfDyadicGridArithmeticV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T10:08:39.267356+00:00
-- url     : https://prove2.me/theorems/f6d4ddc1-1434-4781-a323-415ee6e76c38
-- title:
--   Scaled dyadic partition endpoints, order and reflection
-- statement:
--   Use 2^n>0, the finite index bounds and the identity i.rev.val=2^n-i.val. The scaled grid is monotone, contains 0 and t, and is invariant under reflection.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.5; dyadic and limit children of f3decb5b-3c0d-4063-b885-79044b1ecb2f.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDyadicGridArithmeticV1
    (t : NNReal) (n : ℕ) :
    let q : Fin (2 ^ n + 1) → NNReal := fun i => ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)))
    Monotone q ∧ q 0 = 0 ∧ q (Fin.last (2 ^ n)) = t ∧
      (∀ i, q i ≤ t) ∧ ∀ i, q i.rev = t - q i := by sorry
