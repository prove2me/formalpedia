-- Prove2me | Theorems.Thm_MazurCampaign_exceptional_cubic_finite
-- name    : MazurCampaign.exceptional_cubic_finite
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T08:48:03.81189+00:00
-- url     : https://prove2.me/theorems/f4bc6ae9-a1fa-48ce-a704-5428c0939de2
-- title:
--   The exceptional cubic has finite rational point group
-- statement:
--   The rational point group of the elliptic curve $$C:\quad y^2=x^3+2x^2-3x$$ is finite. This is finiteness of all rational points, used with an independent good-reduction bound to classify the exceptional cubic and exclude a subgroup of type $C_2\times C_{12}$.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/NumberTheory/ExceptionalCubicDescent.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.exceptional_cubic_finite :
    Finite (⟨0, 2, 0, -3, 0⟩ : WeierstrassCurve ℚ).toAffine.Point := by sorry
