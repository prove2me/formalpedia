-- Prove2me | Theorems.Thm_OAI_Release075_TriangleSphere_Dipole_delete
-- name    : OAI.Release075.TriangleSphere.Dipole.delete
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:15:36.953317+00:00
-- url     : https://prove2.me/theorems/27ca41ab-f7d0-45a1-9ab7-ce2967927f7d
-- title:
--   Deleting a dipole from a sphere preserves cyclic face sums
-- statement:
--   A triangle sphere is a finite labelled planar map (darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality $\mathrm{cyc}(r)+\mathrm{cyc}(n)+\mathrm{cyc}(rn)=|\text{darts}|+2\,\mathrm{comp}$) all of whose faces are triangles of the face relation, with flip-compatible labels and colours constant along $rn$. A dipole is a pair of faces sharing an edge with mirrored labels. Let $F:E^3\to M$ take values in an abelian group, be invariant under rotating face triples and change sign under mirroring:
--   $$
--   F(b,c,a)=F(a,b,c),\qquad F(\bar a,\bar c,\bar b)=-F(a,b,c)
--   $$
--   for faces $(a,b,c)$. If the sphere has a dipole, then there is a sphere with fewer darts and the same corner sum $\sum_aF(\mathrm{label}\,a,\mathrm{label}\,na,\mathrm{label}\,n^2a)$.
--
--   Such evaluations are therefore determined by dipole-free spheres.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Spheres.lean#L272-L357

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
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem OAI.Release075.TriangleSphere.Dipole.delete {D : TriangleSphere flip color face} (P : D.Dipole)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c) :
    ∃ D' : TriangleSphere flip color face,
      Fintype.card D'.Dart < Fintype.card D.Dart ∧ D'.cornerSum F = D.cornerSum F := by sorry
