-- Prove2me | Theorems.Thm_OAI_OddGoldbach23_medium_count
-- name    : OAI.OddGoldbach23.medium_count
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:57:21.738988+00:00
-- url     : https://prove2.me/theorems/2744f32e-1b40-40c9-9d02-98986839a493
-- title:
--   Two-prime counting bound in the medium range
-- statement:
--   For every natural number n with 20 ≤ log n ≤ 300, the number of integers s between 0 and n inclusive that are representable as a sum of two odd primes is at least 100n/2199. Representable integers are counted once, regardless of the number of representations.
-- source:
--   Numerical refinement of the existing Schnirelmann–Mann/Riesel–Vaughan formalization, supporting https://prove2.me/theorems/82fdb6cc-2eda-4f2c-a3d7-72dacecba417 . Exact interval and polynomial checks, 2026-10-25.

import Mathlib
import Definitions.Def_Schnir_defs

theorem OAI.OddGoldbach23.medium_count (n : ℕ) (h1 : 20 ≤ Real.log n) (h2 : Real.log n ≤ 300) :
    (n : ℝ) * (100 / 2199) ≤ (((Finset.range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) := by sorry
