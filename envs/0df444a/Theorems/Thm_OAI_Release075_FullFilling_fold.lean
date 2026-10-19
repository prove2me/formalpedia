-- Prove2me | Theorems.Thm_OAI_Release075_FullFilling_fold
-- name    : OAI.Release075.FullFilling.fold
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:19:24.716661+00:00
-- url     : https://prove2.me/theorems/5357fd52-3dc5-4953-ab0d-1be7475a5b77
-- title:
--   Folding a cancelling boundary pair preserves the trace
-- statement:
--   A full filling of a word $w$ is a labelled planar map with a boundary cycle spelling $w$ in which every non-boundary dart, in every component, lies on a triangle of the face relation or on an isolated bigon ($na=ra$, $n^2a=a$). Its trace for $F:E^3\to M$ (an abelian group) is $\sum_{a\notin\text{boundary}}F(\mathrm{label}\,a,\mathrm{label}\,na,\mathrm{label}\,n^2a)$. Suppose flip is an involution, $\mathrm{color}(e)\ne\mathrm{color}(\mathrm{flip}\,e)$, $F(a,b,a)=0$, and $D$ has boundary $b,a,c_1,\dots,c_k$ with $\mathrm{label}(a)=\mathrm{flip}(\mathrm{label}(b))$. Then there is a full filling $D'$ of the shorter word $\mathrm{label}(c_1)\cdots\mathrm{label}(c_k)$ with
--   $$
--   \mathrm{trace}(D')=\mathrm{trace}(D).
--   $$
--
--   All components are kept, and the folded pair becomes an isolated bigon.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/FullFilling.lean#L259-L325

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

theorem OAI.Release075.FullFilling.fold {w : List E} (D : FullFilling flip color face w)
    (hflip : Function.Involutive flip) (hne : ∀ e, color e ≠ color (flip e))
    {a b : D.Dart} {l : List D.Dart} (hb : D.boundary = b::a::l)
    (hl : D.label a = flip (D.label b)) (F : E → E → E → M)
    (hdeg : ∀ a b, F a b a = 0) :
    ∃ D' : FullFilling flip color face (l.map D.label), D'.trace F = D.trace F := by sorry
