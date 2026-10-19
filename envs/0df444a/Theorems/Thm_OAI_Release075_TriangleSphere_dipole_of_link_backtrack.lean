-- Prove2me | Theorems.Thm_OAI_Release075_TriangleSphere_dipole_of_link_backtrack
-- name    : OAI.Release075.TriangleSphere.dipole_of_link_backtrack
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:13:51.582226+00:00
-- url     : https://prove2.me/theorems/ecd517e2-8231-4379-9d5a-316b8eabb631
-- title:
--   A link backtrack on a triangle sphere produces a dipole
-- statement:
--   A triangle sphere is a finite labelled planar map (darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality $\mathrm{cyc}(r)+\mathrm{cyc}(n)+\mathrm{cyc}(rn)=|\text{darts}|+2\,\mathrm{comp}$) all of whose faces are triangles of the face relation, with flip-compatible labels and colours constant along $rn$. A dipole is a pair of faces sharing an edge with mirrored labels. Assume faces have three distinct colours, flip is an involution, faces are mirror-invariant ($\mathrm{face}(a,b,c)\Rightarrow\mathrm{face}(\bar a,\bar c,\bar b)$), and a face is determined by two consecutive sides. If some dart $x$ satisfies the backtrack condition
--   $$
--   \mathrm{label}(x)=\mathrm{label}\bigl((rn)^2x\bigr),
--   $$
--   then the sphere contains a dipole.
--
--   Hence in a dipole-free sphere every corner walk around a vertex is reduced.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Spheres.lean#L62-L105

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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres

open OAI OAI.Release075 OAI.Release075.TriangleSphere
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable (D : TriangleSphere flip color face)

theorem OAI.Release075.TriangleSphere.dipole_of_link_backtrack
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hflip : ∀ e, flip (flip e) = e)
    (hmirror : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (hunique : ∀ a b c c', face a b c → face a b c' → c = c')
    (x : D.Dart)
    (hback : D.label x = D.label ((D.reverse*D.next) ((D.reverse*D.next) x))) :
    Nonempty D.Dipole := by sorry
