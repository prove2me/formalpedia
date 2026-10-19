-- Prove2me | Theorems.Thm_OAI_Release075_TriangleFilling_dipole_of_link_backtrack
-- name    : OAI.Release075.TriangleFilling.dipole_of_link_backtrack
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:02:14.496297+00:00
-- url     : https://prove2.me/theorems/0a8a7d7e-665d-4f7f-95ed-50669ed12064
-- title:
--   A backtrack in a vertex link produces a dipole
-- statement:
--   A triangle filling of a word $w$ over an edge alphabet $E$ (with a flip $E\to E$, a vertex colouring of edges by their targets, and a ternary face relation) is a finite planar map: darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality, labels with $\mathrm{label}(rd)=\mathrm{flip}(\mathrm{label}(d))$ and colours constant along $rn$, and a boundary cycle of $n$ spelling $w$, such that every non-boundary dart in a component meeting the boundary lies on a triangular face of the face relation. A word is fillable if it has a triangle filling. Assume faces have three distinct colours, flip is an involution, faces are mirror-invariant ($\mathrm{face}(a,b,c)\Rightarrow\mathrm{face}(\bar a,\bar c,\bar b)$), and a face is determined by two consecutive sides. Let $x$ be an active dart such that $x$ and $(rn)x$ are not on the boundary and the corner walk around the vertex backtracks:
--   $$
--   \mathrm{label}(x)=\mathrm{label}\bigl((rn)^2x\bigr).
--   $$
--   Then the filling contains a dipole.
--
--   Hence in a filling without dipoles the corner walks around interior vertices are reduced.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Dipoles.lean#L187-L245

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

theorem OAI.Release075.TriangleFilling.dipole_of_link_backtrack
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (x : D.Dart) (hx : D.Active x) (hnx : x ∉ D.boundary)
    (hnb : (D.reverse*D.next) x ∉ D.boundary)
    (hback : D.label x = D.label ((D.reverse*D.next) ((D.reverse*D.next) x))) :
    Nonempty D.Dipole := by sorry
