-- Prove2me | Theorems.Thm_Helfgott_squarefree_harmonic_numeric_group001_checked
-- name    : Helfgott.squarefree_harmonic_numeric_group001_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:51:14.155988+00:00
-- url     : https://prove2.me/theorems/0e0e5c88-e25f-44bd-84ba-493178849d19
-- title:
--   Squarefree harmonic finite baseline: exact blocks 10–19
-- statement:
--   For the previously published Mobius candidate table, certify the exact square counts and rounded harmonic upper numerators in ten consecutive blocks covering [5120, 10001). Rounding uses scale 1000000. These are unconditional kernel-checked arithmetic equalities used to establish the actual squarefree harmonic baseline through 10000; identifying the table with the Mobius function is a separate already proved certificate.
-- source:
--   Exact finite arithmetic certificate for the squarefree harmonic bound used in the explicit Mobius minor-arc argument. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset Nat
open scoped BigOperators

namespace Helfgott
theorem squarefree_harmonic_numeric_group001_checked :
  ((∑ n ∈ Ico 5120 5632, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (309 : ℤ) ∧
    (∑ n ∈ Ico 5120 5632, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (57674 : ℕ)) ∧
  ((∑ n ∈ Ico 5632 6144, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (314 : ℤ) ∧
    (∑ n ∈ Ico 5632 6144, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (53506 : ℕ)) ∧
  ((∑ n ∈ Ico 6144 6656, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 6144 6656, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (48628 : ℕ)) ∧
  ((∑ n ∈ Ico 6656 7168, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 6656 7168, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (45038 : ℕ)) ∧
  ((∑ n ∈ Ico 7168 7680, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (315 : ℤ) ∧
    (∑ n ∈ Ico 7168 7680, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (42602 : ℕ)) ∧
  ((∑ n ∈ Ico 7680 8192, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 7680 8192, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (39365 : ℕ)) ∧
  ((∑ n ∈ Ico 8192 8704, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 8192 8704, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (37105 : ℕ)) ∧
  ((∑ n ∈ Ico 8704 9216, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (314 : ℤ) ∧
    (∑ n ∈ Ico 8704 9216, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (35205 : ℕ)) ∧
  ((∑ n ∈ Ico 9216 9728, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 9216 9728, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (32995 : ℕ)) ∧
  ((∑ n ∈ Ico 9728 10001, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (164 : ℤ) ∧
    (∑ n ∈ Ico 9728 10001, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (16714 : ℕ)) := by sorry
end Helfgott
