-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingMechanismExpLaplaceIdentity
-- name    : Kyprianou.Ch01.branchingMechanismExpLaplaceIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:24:40.74342+00:00
-- url     : https://prove2.me/theorems/55bcee2d-a0d9-48d4-94c1-1e3a5c90f5a0
-- title:
--   Branching mechanism exponential offspring transform identity without moment assumptions
-- statement:
--   For arbitrary offspring PMF and q>0, the sum of p_k(1-exp(-q(k-1))) equals 1-exp(q) times the discrete Laplace transform of the offspring. Summability follows because exp(-qk)≤1 and the PMF has total mass one. The identity is algebraic and makes no finite offspring mean assumption.
-- source:
--   Extracted verbatim from the already Proved Kyprianou.Ch01.branchingOneAncestorWeightedRateIdentity, its internal helper WRIAux.mom, UUID a28155cc-a558-461d-87fb-452204f94206.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingMechanismExpLaplaceIdentity
    (offspring : PMF ℕ) (q : ℝ) (hq : 0 < q) :
    (∑' k : ℕ,
      (offspring k).toReal *
        (1 - Real.exp (-q * ((k : ℝ) - 1)))) =
      1 - Real.exp q *
        (∑' k : ℕ,
          (offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
  sorry
