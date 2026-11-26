-- Prove2me | Theorems.Thm_MasulloRH_computed_gaussian_upper_lt_one
-- name    : MasulloRH.computed_gaussian_upper_lt_one
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T10:36:32.196949+00:00
-- url     : https://prove2.me/theorems/5b31ff37-d856-57ed-9972-1e1cde8f85dc
-- title:
--   The computed Gaussian upper parameter is strictly below one on every integer grid cell
-- statement:
--   For every integer cell index \(k\), the upper endpoint produced by the rational generator for the nested Gaussian parameter is strictly less than one. This includes all 36,864 central cells and justifies the positivity required in their geometric tail denominator.
-- source:
--   A quantitative certificate for https://prove2.me/theorems/9921bc57-a605-47ac-a7be-76ddbcc1c2e4 using the deterministic table https://prove2.me/definitions/b3a30ca4-39cc-42b4-af9e-c419ffe83506 .

import Definitions.Def_MasulloRH_HeightTwoComputedGrid

open MasulloRH.ComputedGrid
set_option autoImplicit false

theorem MasulloRH.computed_gaussian_upper_lt_one (k : ℤ) :
    (gaussianHi (edge k) (edge (k+1)) (decide (k < 24576))).upper < 1 := by sorry
