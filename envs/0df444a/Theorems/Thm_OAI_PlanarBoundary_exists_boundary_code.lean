-- Prove2me | Theorems.Thm_OAI_PlanarBoundary_exists_boundary_code
-- name    : OAI.PlanarBoundary.exists_boundary_code
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:48:02.436069+00:00
-- url     : https://prove2.me/theorems/5e0c6fa7-097f-4446-bfa7-d7f4381828a9
-- title:
--   Boundaries around the origin are encoded by codes
-- statement:
--   For a finite set $X\subseteq\mathbb Z^2$ of unit cells, the boundary consists of the counterclockwise-oriented sides of cells in $X$ whose outward neighbour is not in $X$; each side has a tail and a head corner, an inside cell and an outside cell. A code of length $n$ is a starting column below $2n$, a starting row and a word of $n$ directions, tracing $n$ consecutive unit sides; it is valid if the traced sides are distinct boundary sides of some finite cell set. A code is blocked at $\omega$ if each traced side has a bad inner or outer cell. If $(0,0)\in X$, there is a code $c$ of some length $n>0$ whose traced sides are $n$ distinct boundary sides of $X$:
--   $$
--   \mathrm{side}_i(c)=e_i\in\partial X,\quad e_i\ \text{distinct}.
--   $$
--
--   So the number of possible contours of length $n$ is at most the number of codes, $4n\cdot4^n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean#L364-L394

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

open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical
open Classical

theorem OAI.PlanarBoundary.exists_boundary_code (X : Finset Point) (hX : (0,0) ∈ X) :
    ∃ n : ℕ, ∃ _hn : 0 < n, ∃ c : Code n, ∃ e : Fin n → Boundary X,
      Function.Injective e ∧ ∀ i, traceSide c i = (e i).val := by sorry
