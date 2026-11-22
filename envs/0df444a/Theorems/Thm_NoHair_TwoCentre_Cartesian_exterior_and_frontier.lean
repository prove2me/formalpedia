-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Cartesian_exterior_and_frontier
-- name    : NoHair.TwoCentre.Cartesian.exterior_and_frontier
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T21:38:16.014101+00:00
-- url     : https://prove2.me/theorems/0de0590b-43e7-4842-bb91-2326e3abdd84
-- title:
--   The full two-centre exterior has a single connected frontier in the chosen extension
-- statement:
--   The given change of time and radial coordinates maps the entire two-centre isotropic exterior diffeomorphically onto $\{|X|>1,\ X\ne3e_1\}$. In the extended spacetime $M=\{(v,X):|X|>3/4,\ X\ne3e_1\}$ the relative frontier of that exterior is exactly $\{|X|=1\}$. This frontier is connected. The excluded second pole contributes no frontier points in $M$. The identification of this exterior with the chronological past of the asymptotic end is a further causal assertion.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696. The relative-topology construction uses the explicitly defined open submanifold.

import Definitions.Def_NoHair_TwoCentreSpacetime
import Definitions.Def_NoHair_spacetime

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian Set

theorem NoHair.TwoCentre.Cartesian.exterior_and_frontier :
    IsOpen spacetime ∧ IsDiffeoOnto toAdvanced exterior outerRegion ∧
    frontier {z : spacetime | (z : E4) ∈ outerRegion} = {z : spacetime | (z : E4) ∈ horizon} ∧
    IsConnected {z : spacetime | (z : E4) ∈ horizon} := by
  sorry
