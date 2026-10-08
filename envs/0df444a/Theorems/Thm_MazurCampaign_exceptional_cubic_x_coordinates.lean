-- Prove2me | Theorems.Thm_MazurCampaign_exceptional_cubic_x_coordinates
-- name    : MazurCampaign.exceptional_cubic_x_coordinates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T08:49:30.891413+00:00
-- url     : https://prove2.me/theorems/cc5d1ea5-0ea7-4fab-a555-3f95543e623f
-- title:
--   Rational coordinates on the exceptional cubic
-- statement:
--   Every rational point $(X,Y)$ on the cubic $$Y^2=(X-10)(X-6)(X+6)$$ has $$X\in\{-6,2,6,10,18\}.$$ This exact coordinate restriction is the exceptional-cubic input to the unconditional exclusion of $C_2\times C_{12}$ in rational elliptic-curve torsion.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/NumberTheory/ExceptionalCubicDescent.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.exceptional_cubic_x_coordinates :
    ∀ X Y : ℚ, Y ^ 2 = (X - 10) * (X - 6) * (X + 6) →
      X = -6 ∨ X = 2 ∨ X = 6 ∨ X = 10 ∨ X = 18 := by sorry
