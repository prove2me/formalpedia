-- Prove2me | Theorems.Thm_OAI_Release075_TriangleFilling_wedge
-- name    : OAI.Release075.TriangleFilling.wedge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:59:37.30351+00:00
-- url     : https://prove2.me/theorems/5cd02b53-4dae-4b95-9ed6-8de0e6a8f324
-- title:
--   Wedging two fillings at their first boundary corners
-- statement:
--   A triangle filling of a word $w$ over an edge alphabet $E$ (with a flip $E\to E$, a vertex colouring of edges by their targets, and a ternary face relation) is a finite planar map: darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality, labels with $\mathrm{label}(rd)=\mathrm{flip}(\mathrm{label}(d))$ and colours constant along $rn$, and a boundary cycle of $n$ spelling $w$, such that every non-boundary dart in a component meeting the boundary lies on a triangular face of the face relation. A word is fillable if it has a triangle filling. Let $D$ fill $w$ with boundary starting at $a$, and $D'$ fill $w'$ with boundary starting at $b$. Suppose the initial corners have the same colour:
--   $$
--   \mathrm{color}(\mathrm{flip}(\mathrm{label}\,a))=\mathrm{color}(\mathrm{flip}(\mathrm{label}\,b)).
--   $$
--   Then the concatenation $w\,w'$ is fillable.
--
--   Components of either filling that miss its boundary do not become active.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/TriangleFilling.lean#L317-L445

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

open OAI OAI.Release075 OAI.Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem OAI.Release075.TriangleFilling.wedge {w w' : List E} (D : TriangleFilling flip color face w)
    (D' : TriangleFilling flip color face w')
    {a : D.Dart} {b : D'.Dart} {l : List D.Dart} {l' : List D'.Dart}
    (ha : D.boundary = a::l) (hb : D'.boundary = b::l')
    (hc : color (flip (D.label a)) = color (flip (D'.label b))) :
    Nonempty (TriangleFilling flip color face (w++w')) := by sorry
