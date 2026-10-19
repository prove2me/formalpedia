-- Prove2me | Theorems.Thm_OAI_LatticeRelay_translation_face
-- name    : OAI.LatticeRelay.translation_face
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:37:28.683479+00:00
-- url     : https://prove2.me/theorems/d71749ce-a6f5-4573-af47-e089f7d11d83
-- title:
--   Translation steps move quarter-faces forward along the axis
-- statement:
--   In $\mathbb Z^3$, $\mathrm{Rect}(c,w)=\{x:|x_i-c_i|\le w_i\}$, and a quarter-face of the cube of size $s$ around $u$ lies in a face plane $x_h=u_h\pm s$ with the other coordinates in half-ranges of length $s$; inward signs point towards $0$. If $s\le w$ and $u$ lies in the cube of radius $w$ around $(a,0,0)$, then the quarter-face of size $s$ around $u$ with normal $e_0$, pointing forward in coordinate $0$ and inward in the others, lies in the cube of radius $w$ around $(a+s,0,0)$:
--   $$
--   \mathrm{QF}(u,s,0,\mathrm{fwd}(u))\subseteq\mathrm{Cube}\bigl((a+s,0,0),w\bigr).
--   $$
--
--   This handles the translation steps of the relay route.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Relay.lean#L110-L125

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

open OAI OAI.LatticeRelay
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open Set

theorem OAI.LatticeRelay.translation_face {a s w : ℤ} (hs : s ≤ w) {u : Vertex}
    (hu : u ∈ Cube (axisCenter a) w) :
    QuarterFace u s 0 (forwardInward u) ⊆ Cube (axisCenter (a+s)) w := by sorry
