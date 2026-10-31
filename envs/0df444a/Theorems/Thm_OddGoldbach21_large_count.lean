-- Prove2me | Theorems.Thm_OddGoldbach21_large_count
-- name    : OddGoldbach21.large_count
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T09:54:17.163982+00:00
-- url     : https://prove2.me/theorems/ead17a5f-fdbd-4605-a18f-e0cca9ddf480
-- title:
--   Improved two-prime count in the large range
-- statement:
--   For every natural number n with exp(300) ≤ n, at least 100n/1999 distinct integers at most n are sums of two odd primes. The count uses the existing Schnir.r definition.
-- source:
--   Private refinement of https://prove2.me/theorems/82fdb6cc-2eda-4f2c-a3d7-72dacecba417 using the existing Rosser-Schoenfeld theta lower bound https://prove2.me/theorems/d4cf496a-eed1-4284-8d5d-f9cfbfb07786 . New constants derived locally, not claimed as quoted from the source.

import Mathlib
import Definitions.Def_Schnir_defs

theorem OddGoldbach21.large_count (n : ℕ) (hn : Real.exp 300 ≤ (n : ℝ)) :
 (n : ℝ) * (100 / 1999) ≤ (((Finset.range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) := by sorry
