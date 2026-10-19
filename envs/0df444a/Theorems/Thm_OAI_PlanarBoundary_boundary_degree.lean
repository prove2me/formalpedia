-- Prove2me | Theorems.Thm_OAI_PlanarBoundary_boundary_degree
-- name    : OAI.PlanarBoundary.boundary_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:50:32.164085+00:00
-- url     : https://prove2.me/theorems/9cfa4efa-06b3-480d-8f54-67c852a78ad8
-- title:
--   Each cell touches at most four boundary sides
-- statement:
--   For a finite set $X\subseteq\mathbb Z^2$ of unit cells, the boundary consists of the counterclockwise-oriented sides of cells in $X$ whose outward neighbour is not in $X$; each side has a tail and a head corner, an inside cell and an outside cell. For every cell $v$, at most four boundary sides have $v$ as their inside or outside cell:
--   $$
--   \#\{e:\ \mathrm{in}(e)=v\ \text{or}\ \mathrm{out}(e)=v\}\le4 .
--   $$
--
--   So each boundary side conflicts with at most seven others.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Matching.lean#L130-L154

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching

open OAI OAI.PlanarBoundary
universe uAlpha uE uV
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical

theorem OAI.PlanarBoundary.boundary_degree (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // primalInside e = v ∨ primalOutside e = v} ≤ 4 := by sorry
