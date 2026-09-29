-- Prove2me | Theorems.Thm_OPG1808_root_problem
-- name    : OPG1808.root_problem
-- status  : Open
-- author  : @hao jia
-- created : 2026-09-07T07:14:27.539719+00:00
-- url     : https://prove2.me/theorems/b62e5450-0c5c-407c-a2f3-9279f3dd4a41
-- title:
--   OPG-1808: rainbow directed triangle or monochromatic source
-- statement:
--   Every nonempty finite tournament whose arcs have three colors has one of the following outcomes:
--
--   1. a cyclically oriented triangle whose three arcs have pairwise distinct colors; or
--   2. a vertex $s$ such that every vertex $t$ is reachable from $s$ by a directed path of one color.
--
--   The color in the second outcome may be selected separately for each target. Rainbow transitive triples are not included in the first outcome.
-- source:
--   Open Problem Garden, Monochromatic reachability versus rainbow triangles, https://www.openproblemgarden.org/op/monochromatic_reachability_vs_rainbow_triangles; attributed there to Sands--Sauer--Woodrow, JCTB 33 (1982), 271-275

import Definitions.Def_opg1808_colored_tournaments

namespace OPG1808

universe u

/-- OPG-1808 for nonempty finite tournaments: either there is a rainbow
directed triangle or a monochromatic source. -/
theorem root_problem
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (htournament : IsTournament D) :
    HasRainbowDirectedTriangle D color ∨
      ∃ s : V, IsMonochromaticSource D color s := by sorry

end OPG1808
