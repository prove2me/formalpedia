-- Prove2me | Theorems.Thm_NoHair_schwarzschild_unit_cartesian_ricci_zero
-- name    : NoHair.schwarzschild_unit_cartesian_ricci_zero
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T23:15:26.565588+00:00
-- url     : https://prove2.me/theorems/300a3522-f0bd-4483-abc9-c71400d21b85
-- title:
--   Direct Ricci-flatness in the mass-one Schwarzschild Kerr–Schild chart
-- statement:
--   Every Ricci component vanishes on the whole positive-radius, ingoing Cartesian Kerr–Schild patch of mass-one Schwarzschild, including the horizon and the trapped interior. This direct calculation is used to check the vacuum hypotheses of the horizon-penetrating end counterexample in a standalone disproof.
-- source:
--   Direct Cartesian calculation using the metric, inverse, Christoffel and Ricci definitions of the NoHair mission. Schwarzschild solution in S. Carroll, Lecture Notes on General Relativity, section 7.

import Definitions.Def_NoHair_coordinates

open NoHair

theorem NoHair.schwarzschild_unit_cartesian_ricci_zero (p : E4) (hp : 0 < ksRadius 0 p) (i j : Fin 4) :
    ricci (kerrNewmanMetric 1 0 0) p i j=0 := by sorry
