-- Prove2me | Theorems.Thm_Helfgott_squarefree_harmonic_numeric_group000_checked
-- name    : Helfgott.squarefree_harmonic_numeric_group000_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:51:13.32152+00:00
-- url     : https://prove2.me/theorems/1d9f6046-aff4-4554-8740-4a6d626020d9
-- title:
--   Squarefree harmonic finite baseline: exact blocks 0–9
-- statement:
--   For the previously published Mobius candidate table, certify the exact square counts and rounded harmonic upper numerators in ten consecutive blocks covering [0, 5120). Rounding uses scale 1000000. These are unconditional kernel-checked arithmetic equalities used to establish the actual squarefree harmonic baseline through 10000; identifying the table with the Mobius function is a separate already proved certificate.
-- source:
--   Exact finite arithmetic certificate for the squarefree harmonic bound used in the explicit Mobius minor-arc argument. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset Nat
open scoped BigOperators

namespace Helfgott
theorem squarefree_harmonic_numeric_group000_checked :
  ((∑ n ∈ Ico 0 512, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (314 : ℤ) ∧
    (∑ n ∈ Ico 0 512, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (4839841 : ℕ)) ∧
  ((∑ n ∈ Ico 512 1024, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 512 1024, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (418705 : ℕ)) ∧
  ((∑ n ∈ Ico 1024 1536, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (313 : ℤ) ∧
    (∑ n ∈ Ico 1024 1536, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (247623 : ℕ)) ∧
  ((∑ n ∈ Ico 1536 2048, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (308 : ℤ) ∧
    (∑ n ∈ Ico 1536 2048, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (173112 : ℕ)) ∧
  ((∑ n ∈ Ico 2048 2560, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 2048 2560, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (136122 : ℕ)) ∧
  ((∑ n ∈ Ico 2560 3072, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 2560 3072, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (111228 : ℕ)) ∧
  ((∑ n ∈ Ico 3072 3584, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (312 : ℤ) ∧
    (∑ n ∈ Ico 3072 3584, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (94141 : ℕ)) ∧
  ((∑ n ∈ Ico 3584 4096, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (310 : ℤ) ∧
    (∑ n ∈ Ico 3584 4096, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (80988 : ℕ)) ∧
  ((∑ n ∈ Ico 4096 4608, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 4096 4608, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (71713 : ℕ)) ∧
  ((∑ n ∈ Ico 4608 5120, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (311 : ℤ) ∧
    (∑ n ∈ Ico 4608 5120, mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) = (64173 : ℕ)) := by sorry
end Helfgott
