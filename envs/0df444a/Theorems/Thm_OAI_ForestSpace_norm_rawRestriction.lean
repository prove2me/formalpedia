-- Prove2me | Theorems.Thm_OAI_ForestSpace_norm_rawRestriction
-- name    : OAI.ForestSpace.norm_rawRestriction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:18:41.55273+00:00
-- url     : https://prove2.me/theorems/5a12a1d2-27ac-487b-ad0a-92f00adb5dfb
-- title:
--   Restricting a dual functional of $J(V)$ to finitely supported vectors preserves its norm
-- statement:
--   Let $V$ be a partially ordered set, let $c_{00}(V)$ be the space of finitely supported functions $V\to\mathbb{R}$ with the disjoint-segment norm, let $J(V)$ be its completion and $\iota:c_{00}(V)\to J(V)$ the canonical isometric embedding, and let $J(V)^*$ be the full continuous dual of $J(V)$ with the operator norm.
--
--   **Theorem.** For every $x\in J(V)^*$, the restriction $x\circ\iota$ is a bounded linear functional on $c_{00}(V)$ with
--   $$
--   \|x\circ\iota\|=\|x\| .
--   $$
--
--   Thus the norm of a functional on the completed space can be computed by testing it on finitely supported vectors only. This is the basis for choosing finitely supported norming vectors and for bounding dual evaluations of the corrected test vectors in the forest-space argument.
--
--   **Formalization Note** The restriction is `rawRestriction x`, the composition of `x` with `UniformSpace.Completion.toComplL`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Polar.lean#L22-L34

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [PartialOrder V]

theorem OAI.ForestSpace.norm_rawRestriction (x : FullDual V) : ‖rawRestriction x‖ = ‖x‖ := by sorry
