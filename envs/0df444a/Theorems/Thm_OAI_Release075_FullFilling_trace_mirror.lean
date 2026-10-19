-- Prove2me | Theorems.Thm_OAI_Release075_FullFilling_trace_mirror
-- name    : OAI.Release075.FullFilling.trace_mirror
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:16:18.399976+00:00
-- url     : https://prove2.me/theorems/e99c7fcd-3979-4f68-b916-3026fd82ac9b
-- title:
--   Mirroring a full filling negates its trace
-- statement:
--   A full filling of a word $w$ is a labelled planar map with a boundary cycle spelling $w$ in which every non-boundary dart, in every component, lies on a triangle of the face relation or on an isolated bigon ($na=ra$, $n^2a=a$). Its trace for $F:E^3\to M$ (an abelian group) is $\sum_{a\notin\text{boundary}}F(\mathrm{label}\,a,\mathrm{label}\,na,\mathrm{label}\,n^2a)$. Suppose flip is an involution, faces are mirror-invariant, $F$ changes sign under mirroring, $F(\bar a,\bar c,\bar b)=-F(a,b,c)$ on faces, and $F$ vanishes on degenerate triples, $F(a,b,a)=0$. Then the mirrored filling (face permutation inverted, labels flipped) of the reversed flipped word satisfies
--   $$
--   \mathrm{trace}(\mathrm{mirror}\,D)=-\,\mathrm{trace}(D).
--   $$
--
--   The bigons allowed in full fillings contribute nothing on either side.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/FullFilling.lean#L167-L188

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

open OAI OAI.Release075 OAI.Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : FullFilling flip color face w)

theorem OAI.Release075.FullFilling.trace_mirror (hflip : Function.Involutive flip)
    (hface : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (F : E → E → E → M)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0) :
    (D.mirror hflip hface).trace F = - D.trace F := by sorry
