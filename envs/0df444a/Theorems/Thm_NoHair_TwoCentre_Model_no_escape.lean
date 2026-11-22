-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Model_no_escape
-- name    : NoHair.TwoCentre.Model.no_escape
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:03:45.295807+00:00
-- url     : https://prove2.me/theorems/18553374-0c1f-483f-a4c5-78a60ab0a6f3
-- title:
--   No future timelike curve escapes from the specified two-centre black-hole interior
-- statement:
--   On the concrete one-horizon two-centre manifold, every future timelike $C^1$ curve that starts on the horizon or in the interior ends outside the open exterior. Here the timelike and future inequalities use the exact advanced Cartesian metric and time orientation of the model and the derivative in the mission’s curve definition.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_TwoCentreBlackHole

open NoHair NoHair.TwoCentre.Model Set

theorem NoHair.TwoCentre.Model.no_escape (γ : ℝ → manifold) (hγ : IsFutureTimelikeCurveIn metric orientation univ γ)
    (hstart : γ 0 ∉ outer) : γ 1 ∉ outer := by
  sorry
