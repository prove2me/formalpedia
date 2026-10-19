-- Prove2me | Theorems.Thm_OAI_Release075_TriangleFilling_Dipole_cancel
-- name    : OAI.Release075.TriangleFilling.Dipole.cancel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:01:10.314983+00:00
-- url     : https://prove2.me/theorems/9a8960c8-bc25-4f79-9a12-34b77cd7b607
-- title:
--   Cancelling a dipole decreases the active count
-- statement:
--   A triangle filling of a word $w$ over an edge alphabet $E$ (with a flip $E\to E$, a vertex colouring of edges by their targets, and a ternary face relation) is a finite planar map: darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality, labels with $\mathrm{label}(rd)=\mathrm{flip}(\mathrm{label}(d))$ and colours constant along $rn$, and a boundary cycle of $n$ spelling $w$, such that every non-boundary dart in a component meeting the boundary lies on a triangular face of the face relation. A word is fillable if it has a triangle filling. A dipole in a triangle filling is a pair of interior triangular faces, darts $e_0,e_1,e_2$ and $e_3,e_4,e_5$ with $n$ acting as $(0\,1\,2)(3\,4\,5)$, sharing the edge $r(e_0)=e_3$, with $e_0$ active, adjacent colours different and mirrored labels $\mathrm{label}(e_5)=\mathrm{flip}(\mathrm{label}(e_1))$, $\mathrm{label}(e_4)=\mathrm{flip}(\mathrm{label}(e_2))$. The active count is the number of darts in components meeting the boundary. If a filling $D$ of $w$ contains a dipole, then there is a filling $D'$ of the same word with
--   $$
--   \mathrm{active}(D')<\mathrm{active}(D).
--   $$
--
--   The cancelled pair survives as a separate component away from the boundary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Dipoles.lean#L26-L84

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

theorem OAI.Release075.TriangleFilling.Dipole.cancel {w : List E} {D : TriangleFilling flip color face w} (P : D.Dipole) :
    ∃ D' : TriangleFilling flip color face w, D'.activeCount < D.activeCount := by sorry
