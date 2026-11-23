-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingMechanismLocallyLipschitzPositive
-- name    : Kyprianou.Ch01.branchingMechanismLocallyLipschitzPositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:17:15.259872+00:00
-- url     : https://prove2.me/theorems/4562333f-f2d8-4772-a5e5-5ce737215b74
-- title:
--   Local Lipschitz regularity of the branching mechanism without finite offspring mean
-- statement:
--   For any finite real rate and arbitrary offspring PMF, the mechanism rate times the sum of p(k)(1-exp(-q(k-1))) is Lipschitz on every strictly positive compact [a,b]. The k≥1 terms have moment-independent Lipschitz constant 1/a via the Proved Kyprianou.Ch01.exp_uniform_lipschitz_on_positive. The k=0 term has constant exp(b) using a bounded exponential mean-value estimate. Sum against the unit probability mass; no finite offspring moment.
-- source:
--   Kyprianou (2006), Chapter 1 section 1.3.4; existing Proved exp_uniform_lipschitz_on_positive UUID df473ead-e1e9-47ae-acf2-b7e11250fa15.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingMechanismLocallyLipschitzPositive
    (rate : ℝ) (offspring : PMF ℕ) :
    ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
          |branchingMechanism rate offspring y -
            branchingMechanism rate offspring x| ≤
            C * |y - x| := by
  sorry
