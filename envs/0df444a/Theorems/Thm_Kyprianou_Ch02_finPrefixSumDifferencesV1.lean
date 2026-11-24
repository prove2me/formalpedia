-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finPrefixSumDifferencesV1
-- name    : Kyprianou.Ch02.finPrefixSumDifferencesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:21:54.013001+00:00
-- url     : https://prove2.me/theorems/27cb29a1-6aec-4cad-acd2-dbf809b33d2e
-- title:
--   Finite prefix sum of consecutive differences
-- statement:
--   Induct along the finite index j. In the successor case the prefix filter adds exactly the next index; the resulting sum telescopes.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.finPrefixSumDifferencesV1
    (n : ℕ) (a : Fin (n+1) → ℝ) (h0 : a 0 = 0) (j : Fin (n+1)) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j.val),
      (a i.succ - a i.castSucc)) = a j := by sorry
