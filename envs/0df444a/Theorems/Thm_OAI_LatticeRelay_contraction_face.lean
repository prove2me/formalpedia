-- Prove2me | Theorems.Thm_OAI_LatticeRelay_contraction_face
-- name    : OAI.LatticeRelay.contraction_face
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:36:43.173655+00:00
-- url     : https://prove2.me/theorems/33c84b6d-e5b8-4d31-8f09-bd42d6a45ccf
-- title:
--   Contraction steps keep quarter-faces inside the next rectangle
-- statement:
--   In $\mathbb Z^3$, $\mathrm{Rect}(c,w)=\{x:|x_i-c_i|\le w_i\}$, and a quarter-face of the cube of size $s$ around $u$ lies in a face plane $x_h=u_h\pm s$ with the other coordinates in half-ranges of length $s$; inward signs point towards $0$. Let $r,a\ge0$, $h$ a coordinate and $u$ with $|u_i|\le2r+a$ for $i<h$ and $|u_i|\le4r+a$ otherwise. Then the inward quarter-face of size $2r$ around $u$ in direction $h$ lies in the rectangle centred at $0$ with widths $2r+a$ for $i\le h$ and $4r+a$ for $i>h$:
--   $$
--   \mathrm{QF}(u,2r,h,\mathrm{inward}(u))\subseteq\mathrm{Rect}\bigl(0,\ (2r+a)_{i\le h},(4r+a)_{i>h}\bigr).
--   $$
--
--   This handles the first three steps of the relay route.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Relay.lean#L62-L83

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

theorem OAI.LatticeRelay.contraction_face {r a : ℤ} (hr : 0 ≤ r) (ha : 0 ≤ a) (h : Fin 3)
    {u : Vertex}
    (hu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a) :
    QuarterFace u (2*r) h (inward u) ⊆
      Rect 0 (fun i => if i ≤ h then 2*r+a else 4*r+a) := by sorry
