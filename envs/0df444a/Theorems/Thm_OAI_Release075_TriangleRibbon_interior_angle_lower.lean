-- Prove2me | Theorems.Thm_OAI_Release075_TriangleRibbon_interior_angle_lower
-- name    : OAI.Release075.TriangleRibbon.interior_angle_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:04:39.893985+00:00
-- url     : https://prove2.me/theorems/b2567e45-c853-4d08-9ab1-16c618792afb
-- title:
--   Interior vertex angles are bounded by closed link walks
-- statement:
--   Let $R$ be a triangle ribbon: darts with a reverse involution and a face permutation, a distinguished outer face, vertices given by the cycles of $\mathrm{reverse}\cdot\mathrm{face}$ coloured in $\{0,1,2\}$, and inner faces whose corners carry all three colours. Corners on inner faces have angle $3$ at colour $0$ and $1$ otherwise. Let corner labels in a graph $L$ be given such that consecutive inner corners around a vertex are adjacent in $L$ and the walk never backtracks across two consecutive inner corners. Suppose every nonempty reduced closed walk $p$ in $L$ based at the label of a corner $a$ satisfies $M\le w(a)\cdot\mathrm{length}(p)$, where $w(a)\in\{3,1\}$ is the angle weight of the vertex colour of $a$. Then every vertex $v$ with no boundary visit has
--   $$
--   \theta(v)\ge M .
--   $$
--
--   The corner walk is closed and nonempty because the vertex has no outer corner.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Ribbons.lean#L615-L652

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

theorem OAI.Release075.TriangleRibbon.interior_angle_lower (M : ℝ)
    (hclosed : ∀ a (p : L.Walk (label a) (label a)), 0 < p.length → ReducedWalk p →
      M ≤ weight (R.color (cl R.vertexPerm a)) * p.length)
    (v : R.Vertex) (hv : R.visits v = 0) : M ≤ R.angles v := by sorry
