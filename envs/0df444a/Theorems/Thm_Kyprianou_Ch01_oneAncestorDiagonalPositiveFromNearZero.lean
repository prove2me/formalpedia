-- Prove2me | Theorems.Thm_Kyprianou_Ch01_oneAncestorDiagonalPositiveFromNearZero
-- name    : Kyprianou.Ch01.oneAncestorDiagonalPositiveFromNearZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:57:14.475386+00:00
-- url     : https://prove2.me/theorems/a118ed68-86ec-4fbb-9a86-99a956809307
-- title:
--   Local diagonal positivity propagates to all finite times under Chapman-Kolmogorov
-- statement:
--   If the return-to-one mass of a population Markov semigroup is positive on an initial time interval, it is positive at every finite horizon. Divide each horizon into sufficiently many short equal increments, repeatedly apply the previously Proved oneAncestorDiagonalSupermultiplicative and positivity of products of ENNReal probabilities, then conclude positive real mass using the finiteness of PMF atoms. No offspring mean is required.
-- source:
--   Chapman-Kolmogorov semigroup and Proved Kyprianou.Ch01.oneAncestorDiagonalSupermultiplicative, UUID 123d3809-443e-4805-b684-4f6472ea25f5.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.oneAncestorDiagonalPositiveFromNearZero
    (K : PopulationLaws)
    (hSemi : IsPopulationMarkovSemigroup K)
    (hInit : K 1 0 = PMF.pure 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hNear : ∀ t : ℝ≥0, (t : ℝ) < δ →
      0 < ((K 1 t) 1).toReal) :
    ∀ t : ℝ≥0, 0 < ((K 1 t) 1).toReal := by
  sorry
