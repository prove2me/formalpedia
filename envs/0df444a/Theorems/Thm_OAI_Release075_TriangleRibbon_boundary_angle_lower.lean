-- Prove2me | Theorems.Thm_OAI_Release075_TriangleRibbon_boundary_angle_lower
-- name    : OAI.Release075.TriangleRibbon.boundary_angle_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:07:04.702662+00:00
-- url     : https://prove2.me/theorems/3764177e-7001-4337-8b4f-6ff898e765ab
-- title:
--   Singly visited boundary vertices have angle at least five
-- statement:
--   Let $R$ be a triangle ribbon: darts with a reverse involution and a face permutation, a distinguished outer face, vertices given by the cycles of $\mathrm{reverse}\cdot\mathrm{face}$ coloured in $\{0,1,2\}$, and inner faces whose corners carry all three colours. Corners on inner faces have angle $3$ at colour $0$ and $1$ otherwise. Let corner labels in a graph $L$ be given such that consecutive inner corners around a vertex are adjacent in $L$ and the walk never backtracks across two consecutive inner corners. Suppose that for every outer corner $a$, every reduced walk $p$ in $L$ from the label of the next corner around the vertex back to the label of $a$ satisfies $5\le w(a)\cdot\mathrm{length}(p)$. Then every vertex $v$ visited exactly once by the boundary has
--   $$
--   \theta(v)\ge5 .
--   $$
--
--   In angle units this says the boundary turns by at least $\pi$ there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Ribbons.lean#L654-L703

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons

open OAI OAI.Release075 OAI.Release075.TriangleRibbon
open Equiv PermCycles
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable (R : TriangleRibbon)
variable {E : Type*} (L : SimpleGraph E) (label : R.Dart → E)
variable (hadj : ∀ a, ¬ R.IsOuter a → L.Adj (label a) (label (R.vertexPerm a)))
variable (hred : ∀ a, ¬ R.IsOuter a → ¬ R.IsOuter (R.vertexPerm a) →
  label a ≠ label (R.vertexPerm (R.vertexPerm a)))
include hadj hred

theorem OAI.Release075.TriangleRibbon.boundary_angle_lower
    (hboundary : ∀ a, R.IsOuter a →
      ∀ p : L.Walk (label (R.vertexPerm a)) (label a), ReducedWalk p →
        5 ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (v : R.Vertex) (hv : R.visits v = 1) : 5 ≤ R.angles v := by sorry
