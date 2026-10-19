-- Prove2me | Theorems.Thm_OAI_Release075_TriangleFilling_reverse_not_sameCycle
-- name    : OAI.Release075.TriangleFilling.reverse_not_sameCycle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:01:44.388987+00:00
-- url     : https://prove2.me/theorems/59765d93-46c2-4e0c-b2b6-1b5077e2ea9a
-- title:
--   A triangle never contains both sides of one edge
-- statement:
--   A triangle filling of a word $w$ over an edge alphabet $E$ (with a flip $E\to E$, a vertex colouring of edges by their targets, and a ternary face relation) is a finite planar map: darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality, labels with $\mathrm{label}(rd)=\mathrm{flip}(\mathrm{label}(d))$ and colours constant along $rn$, and a boundary cycle of $n$ spelling $w$, such that every non-boundary dart in a component meeting the boundary lies on a triangular face of the face relation. A word is fillable if it has a triangle filling. Assume every face has three distinct colours: $\mathrm{face}(a,b,c)$ implies $\mathrm{color}(a),\mathrm{color}(b),\mathrm{color}(c)$ pairwise distinct. Then for every active non-boundary dart $a$ of a filling, $a$ and $r(a)$ do not lie on the same face cycle:
--   $$
--   \neg\ \bigl(a\sim_n r(a)\bigr).
--   $$
--
--   This is what makes the two triangles of a dipole distinct faces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Dipoles.lean#L164-L185

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

open OAI OAI.Release075 OAI.Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

theorem OAI.Release075.TriangleFilling.reverse_not_sameCycle (a : D.Dart) (ha : D.Active a) (hna : a ∉ D.boundary)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a) :
    ¬ D.next.SameCycle a (D.reverse a) := by sorry
