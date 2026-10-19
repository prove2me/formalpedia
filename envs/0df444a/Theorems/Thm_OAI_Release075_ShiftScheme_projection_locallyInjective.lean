-- Prove2me | Theorems.Thm_OAI_Release075_ShiftScheme_projection_locallyInjective
-- name    : OAI.Release075.ShiftScheme.projection_locallyInjective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:48:03.420519+00:00
-- url     : https://prove2.me/theorems/fb6740a8-0fc5-4ab3-b481-7a04e163b248
-- title:
--   The link projection of a shift scheme is locally injective
-- statement:
--   A shift scheme over labels $I$, points $P$ with incidence sets $\mathrm{inc}(z)\subseteq I$ and blocks $B$ assigns to each block $b$ a size $\ge r$, a label set inside $\mathrm{inc}(\mathrm{point}(b))$ with coordinates $c_b$, and a point; each label lies in at most one block over a given point. Its link is the bipartite graph joining $(i,u,v)\in I\times[r]^2$ to $(b,u,j)$ iff $i$ lies in block $b$ and $j=c_b(i)+v$. The projection sends $(i,u,v)\mapsto i$ and $(b,u,j)\mapsto\mathrm{point}(b)$ into the label–point incidence graph. The projection is locally injective: if $y,y'$ are neighbours of a common vertex $x$ in the link and have the same image, then
--   $$
--   y=y' .
--   $$
--
--   Locally injective maps send reduced walks to reduced walks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Presentation.lean#L158-L201

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation

open OAI OAI.Release075 OAI.Release075.ShiftScheme
variable {I P B : Type*} {r : ℕ} {inc : P → Finset I} (d : ShiftScheme I P B r inc)

theorem OAI.Release075.ShiftScheme.projection_locallyInjective : LocallyInjective d.projection := by sorry
