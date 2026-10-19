-- Prove2me | Theorems.Thm_OAI_Release075_FullFilling_trace_empty
-- name    : OAI.Release075.FullFilling.trace_empty
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:17:43.702868+00:00
-- url     : https://prove2.me/theorems/ccc73c3c-c10d-4e43-997d-a8e9e4586f72
-- title:
--   Full fillings of the empty word have zero trace
-- statement:
--   A full filling of a word $w$ is a labelled planar map with a boundary cycle spelling $w$ in which every non-boundary dart, in every component, lies on a triangle of the face relation or on an isolated bigon ($na=ra$, $n^2a=a$). Its trace for $F:E^3\to M$ (an abelian group) is $\sum_{a\notin\text{boundary}}F(\mathrm{label}\,a,\mathrm{label}\,na,\mathrm{label}\,n^2a)$. Assume every dipole-free triangle sphere over the face relation is empty. Let $F$ be invariant under rotation of faces, antisymmetric under mirroring, and zero on degenerate triples $F(a,b,a)$. Then every full filling $D$ of the empty word satisfies
--   $$
--   \mathrm{trace}(D)=0 .
--   $$
--
--   So a closed full filling carries the zero face chain.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/FullFilling.lean#L199-L240

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

theorem OAI.Release075.FullFilling.trace_empty
    (hempty : ∀ D : TriangleSphere flip color face, IsEmpty D.Dipole → IsEmpty D.Dart)
    (F : E → E → E → M)
    (hrot : ∀ a b c, face a b c → F b c a = F a b c)
    (hmir : ∀ a b c, face a b c → F (flip a) (flip c) (flip b) = -F a b c)
    (hdeg : ∀ a b, F a b a = 0)
    (D : FullFilling flip color face []) : D.trace F = 0 := by sorry
