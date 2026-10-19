-- Prove2me | Theorems.Thm_OAI_Release075_FullFilling_wedge
-- name    : OAI.Release075.FullFilling.wedge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:20:34.852579+00:00
-- url     : https://prove2.me/theorems/3abdb537-d839-4cb4-899e-edf56ed3de32
-- title:
--   Wedging full fillings adds their traces
-- statement:
--   A full filling of a word $w$ over an edge alphabet $E$ (with flip, colouring and face relation) is a labelled planar map, with reverse involution $r$ and face permutation $n$, whose boundary cycle spells $w$ and whose other darts all lie on triangles of the face relation or on isolated bigons. Its trace for $F:E^3\to M$ (an abelian group) is $\sum_{a\notin\text{boundary}}F(\mathrm{label}\,a,\mathrm{label}\,na,\mathrm{label}\,n^2a)$. Let $D$ fill $w$ with boundary starting at $a$ and $D'$ fill $w'$ with boundary starting at $b$, and suppose the two initial corners have the same colour, $\mathrm{color}(\mathrm{flip}(\mathrm{label}\,a))=\mathrm{color}(\mathrm{flip}(\mathrm{label}\,b))$. Then for every $F$ there is a full filling $C$ of $w\,w'$ with
--   $$
--   \mathrm{trace}_F(C)=\mathrm{trace}_F(D)+\mathrm{trace}_F(D').
--   $$
--
--   Components of either filling are all kept, including those away from the boundary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/FullGluing.lean#L11-L148

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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing

open OAI OAI.Release075 OAI.Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem OAI.Release075.FullFilling.wedge {w w' : List E} (D : FullFilling flip color face w)
    (D' : FullFilling flip color face w')
    {a : D.Dart} {b : D'.Dart} {l : List D.Dart} {l' : List D'.Dart}
    (ha : D.boundary = a::l) (hb : D'.boundary = b::l')
    (hc : color (flip (D.label a)) = color (flip (D'.label b)))
    (F : E → E → E → M) :
    ∃ C : FullFilling flip color face (w++w'), C.trace F = D.trace F + D'.trace F := by sorry
