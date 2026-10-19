-- Prove2me | Theorems.Thm_OAI_Release075_Fillable_app
-- name    : OAI.Release075.Fillable.app
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:00:09.274736+00:00
-- url     : https://prove2.me/theorems/336bd2eb-f180-4318-99d6-5f42e4fee4ba
-- title:
--   Concatenation of fillable words
-- statement:
--   A triangle filling of a word $w$ over an edge alphabet $E$ (with a flip $E\to E$, a vertex colouring of edges by their targets, and a ternary face relation) is a finite planar map: darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality, labels with $\mathrm{label}(rd)=\mathrm{flip}(\mathrm{label}(d))$ and colours constant along $rn$, and a boundary cycle of $n$ spelling $w$, such that every non-boundary dart in a component meeting the boundary lies on a triangular face of the face relation. A word is fillable if it has a triangle filling. If $u$ and $v$ are fillable and, whenever both are nonempty with first letters $e$ and $f$, these start at the same colour:
--   $$
--   \mathrm{color}(\mathrm{flip}\,e)=\mathrm{color}(\mathrm{flip}\,f),
--   $$
--   then $u\,v$ is fillable.
--
--   Empty words are allowed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/TriangleFilling.lean#L722-L738

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

open OAI OAI.Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem OAI.Release075.Fillable.app {u v : List E} (hu : Fillable flip color face u) (hv : Fillable flip color face v)
    (hbase : ∀ e es f fs, u = e::es → v = f::fs →
      color (flip e) = color (flip f)) : Fillable flip color face (u++v) := by sorry
