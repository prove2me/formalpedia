-- Prove2me | Theorems.Thm_OAI_Release075_FullFilling_trace_unique
-- name    : OAI.Release075.FullFilling.trace_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:21:19.244985+00:00
-- url     : https://prove2.me/theorems/84f30c4d-53b5-48c0-896c-41b0a106e22d
-- title:
--   The trace of a full filling depends only on its boundary word
-- statement:
--   A full filling of a word $w$ over an edge alphabet $E$ (with flip, colouring and face relation) is a labelled planar map, with reverse involution $r$ and face permutation $n$, whose boundary cycle spells $w$ and whose other darts all lie on triangles of the face relation or on isolated bigons. Its trace for $F:E^3\to M$ (an abelian group) is $\sum_{a\notin\text{boundary}}F(\mathrm{label}\,a,\mathrm{label}\,na,\mathrm{label}\,n^2a)$. Assume every dipole-free triangle sphere is empty, flip is an involution with $\mathrm{color}(e)\ne\mathrm{color}(\mathrm{flip}\,e)$, and faces are mirror-invariant. Let $F$ be rotation-invariant on faces, antisymmetric under mirroring, and zero on degenerate triples $F(a,b,a)$. If $w$ is a closed word path, then any two full fillings $D,D'$ of $w$ have
--   $$
--   \mathrm{trace}_F(D)=\mathrm{trace}_F(D').
--   $$
--
--   In the application the trace is the face chain, so the $2$-chain filling a loop is determined by the loop.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/FullGluing.lean#L225-L254

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
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem OAI.Release075.FullFilling.trace_unique
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (hi : Function.Involutive flip) (hn : ∀ e, color e ≠ color (flip e))
    (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    {x : V} {w : List E} (hw : WordPath flip color x x w)
    (D D' : FullFilling flip color face w) : D.trace F = D'.trace F := by sorry
