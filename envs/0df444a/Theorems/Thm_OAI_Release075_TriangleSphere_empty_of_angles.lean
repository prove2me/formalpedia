-- Prove2me | Theorems.Thm_OAI_Release075_TriangleSphere_empty_of_angles
-- name    : OAI.Release075.TriangleSphere.empty_of_angles
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:14:20.404209+00:00
-- url     : https://prove2.me/theorems/67351ea7-2a62-4724-a4e3-fb555d742df7
-- title:
--   A triangle sphere with large vertex angles is empty
-- statement:
--   A triangle sphere is a finite labelled planar map (darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality $\mathrm{cyc}(r)+\mathrm{cyc}(n)+\mathrm{cyc}(rn)=|\text{darts}|+2\,\mathrm{comp}$) all of whose faces are triangles of the face relation, with flip-compatible labels and colours constant along $rn$. A dipole is a pair of faces sharing an edge with mirrored labels. Colour vertices by $\{0,1,2\}$ through a bijection, assume every face has three distinct colours, and give each corner angle $3$ at colour $0$ and $1$ otherwise. If every vertex has total angle at least $10$, then the sphere has no darts:
--   $$
--   \min_v\theta(v)\ge10\ \Longrightarrow\ |\text{darts}|=0 .
--   $$
--
--   A nonempty closed genus-zero triangulated surface must have a vertex of angle less than a full turn ($10$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Spheres.lean#L201-L226

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

theorem OAI.Release075.TriangleSphere.empty_of_angles (q : V ≃ Fin 3)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hmin : ∀ v, 10 ≤ D.vertexAngle q v) : IsEmpty D.Dart := by sorry
