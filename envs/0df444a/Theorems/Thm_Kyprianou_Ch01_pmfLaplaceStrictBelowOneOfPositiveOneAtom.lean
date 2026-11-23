-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pmfLaplaceStrictBelowOneOfPositiveOneAtom
-- name    : Kyprianou.Ch01.pmfLaplaceStrictBelowOneOfPositiveOneAtom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:59:31.997643+00:00
-- url     : https://prove2.me/theorems/6907748d-ae27-431b-bdce-20d42aa117fa
-- title:
--   Discrete Laplace expectation strictly below one when the one-atom probability is positive
-- statement:
--   For any probability mass function p on ℕ with p(1)>0 and any q>0, the exponential transform Σ p(n)exp(−q n) is strictly below the total mass one. Weighted terms are at most unweighted probabilities, and the n=1 inequality is strict. Summable.tsum_lt_tsum_of_nonneg yields the strict overall comparison; no moment assumption.
-- source:
--   General PMF analytic inequality, adapted from the proved private summability and strict tsum inequality in Kyprianou.Ch01.branchingZeroAbsorbing.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.pmfLaplaceStrictBelowOneOfPositiveOneAtom
    (p : PMF ℕ) (q : ℝ) (hq : 0 < q)
    (hp1 : 0 < (p 1).toReal) :
    (∑' n : ℕ,
      (p n).toReal * Real.exp (-q * (n : ℝ))) < 1 := by
  sorry
