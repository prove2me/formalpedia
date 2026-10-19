-- Prove2me | Theorems.Thm_OAI_Release075_FullFilling_trace_cyclic
-- name    : OAI.Release075.FullFilling.trace_cyclic
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T08:21:59.449551+00:00
-- url     : https://prove2.me/theorems/2801f615-fa46-47b2-9745-0fb0c1fa48fb
-- title:
--   Cyclically rotating the corner function preserves the trace
-- statement:
--   A full filling of a word $w$ over an edge alphabet $E$ (with flip, colouring and face relation) is a labelled planar map, with reverse involution $r$ and face permutation $n$, whose boundary cycle spells $w$ and whose other darts all lie on triangles of the face relation or on isolated bigons. Its trace for $F:E^3\to M$ (an abelian group) is $\sum_{a\notin\text{boundary}}F(\mathrm{label}\,a,\mathrm{label}\,na,\mathrm{label}\,n^2a)$. If every non-boundary dart lies on a triangle ($n^3a=a$), then for every $F$,
--   $$
--   \mathrm{trace}\bigl((x,y,z)\mapsto F(y,z,x)\bigr)=\mathrm{trace}(F).
--   $$
--
--   The trace counts each face once per corner, so cyclic reindexing does not change it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/FullGluing.lean#L264-L282

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
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem OAI.Release075.FullFilling.trace_cyclic {w : List E} (D : FullFilling flip color face w)
    (ht : ∀ a, a ∉ D.boundary → (D.next^3) a = a)
    (F : E → E → E → M) : D.trace (fun a b c => F b c a) = D.trace F := by sorry
