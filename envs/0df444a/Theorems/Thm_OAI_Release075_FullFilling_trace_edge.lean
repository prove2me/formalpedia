-- Prove2me | Theorems.Thm_OAI_Release075_FullFilling_trace_edge
-- name    : OAI.Release075.FullFilling.trace_edge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:22:29.990166+00:00
-- url     : https://prove2.me/theorems/a8e64b2d-f151-4c55-8af7-16e5a743cb07
-- title:
--   Stokes formula for antisymmetric edge evaluations
-- statement:
--   A full filling of a word $w$ over an edge alphabet $E$ (with flip, colouring and face relation) is a labelled planar map, with reverse involution $r$ and face permutation $n$, whose boundary cycle spells $w$ and whose other darts all lie on triangles of the face relation or on isolated bigons. Its trace for $F:E^3\to M$ (an abelian group) is $\sum_{a\notin\text{boundary}}F(\mathrm{label}\,a,\mathrm{label}\,na,\mathrm{label}\,n^2a)$. Let $F:E\to M$ satisfy $F(\mathrm{flip}\,e)=-F(e)$. Then the trace of the corner function that only reads the first edge equals minus the boundary sum:
--   $$
--   \sum_{a\notin\text{boundary}}F(\mathrm{label}\,a)=-\sum_{e\in w}F(e).
--   $$
--
--   This is the discrete Stokes formula for the filling.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/FullGluing.lean#L330-L357

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
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M N : Type} [AddCommGroup M] [AddCommGroup N]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem OAI.Release075.FullFilling.trace_edge {w : List E} (D : FullFilling flip color face w)
    (F : E → M) (hf : ∀ e, F (flip e) = -F e) :
    D.trace (fun a _ _ => F a) = -(w.map F).sum := by sorry
