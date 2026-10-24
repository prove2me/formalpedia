-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collisionRate_tendsto_collisionLimit
-- name    : OAI.PiExponent.DeterminantContradiction.collisionRate_tendsto_collisionLimit
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:01:17.89295+00:00
-- url     : https://prove2.me/theorems/3a011ab1-696d-4ebc-9983-c3eded6c7d23
-- title:
--   The collision rate converges to its weighted simplex limit
-- statement:
--   For each fixed admissible datum, the collision rate converges as the height tends to infinity to the explicit value `collisionLimit d`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.collisionRate_tendsto_collisionLimit (nu : Real) (d : FixedData nu) :
    Tendsto (fun H : Real => collisionRate d H) atTop (nhds (collisionLimit d)) := by sorry
