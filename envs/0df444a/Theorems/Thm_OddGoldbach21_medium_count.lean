-- Prove2me | Theorems.Thm_OddGoldbach21_medium_count
-- name    : OddGoldbach21.medium_count
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T09:54:13.183571+00:00
-- url     : https://prove2.me/theorems/15b67083-2a41-4812-aba7-de384b77735f
-- title:
--   Improved two-prime count in the medium range
-- statement:
--   For every natural number n with 19 ≤ log n ≤ 300, at least 100n/1999 distinct integers at most n are sums of two odd primes. The count uses the existing Schnir.r definition.
-- source:
--   Private refinement of https://prove2.me/theorems/82fdb6cc-2eda-4f2c-a3d7-72dacecba417 using the existing Rosser-Schoenfeld theta lower bound https://prove2.me/theorems/d4cf496a-eed1-4284-8d5d-f9cfbfb07786 . New constants derived locally, not claimed as quoted from the source.

import Mathlib
import Definitions.Def_Schnir_defs

theorem OddGoldbach21.medium_count (n : ℕ) (h1 : 19 ≤ Real.log n) (h2 : Real.log n ≤ 300) :
 (n : ℝ) * (100 / 1999) ≤ (((Finset.range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) := by sorry
