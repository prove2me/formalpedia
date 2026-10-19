-- Prove2me | Theorems.Thm_OAI_Release075_TriangleFilling_fold
-- name    : OAI.Release075.TriangleFilling.fold
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:58:49.467982+00:00
-- url     : https://prove2.me/theorems/7d5d2fec-2929-488e-8965-19e46d5325f4
-- title:
--   Folding a cancelling pair off the boundary of a filling
-- statement:
--   A triangle filling of a word $w$ over an edge alphabet $E$ (with a flip $E\to E$, a vertex colouring of edges by their targets, and a ternary face relation) is a finite planar map: darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ satisfying the Euler equality, labels with $\mathrm{label}(rd)=\mathrm{flip}(\mathrm{label}(d))$ and colours constant along $rn$, and a boundary cycle of $n$ spelling $w$, such that every non-boundary dart in a component meeting the boundary lies on a triangular face of the face relation. A word is fillable if it has a triangle filling. Suppose $\mathrm{flip}$ is an involution, $\mathrm{color}(e)\ne\mathrm{color}(\mathrm{flip}\,e)$ for all $e$, and a filling $D$ of $w$ has boundary $b,a,c_1,\dots,c_k$ with $\mathrm{label}(a)=\mathrm{flip}(\mathrm{label}(b))$. Then the shorter word
--   $$
--   \mathrm{label}(c_1)\cdots\mathrm{label}(c_k)
--   $$
--   is fillable.
--
--   So a backtrack at the start of a fillable word can be cancelled.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/TriangleFilling.lean#L205-L253

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

open OAI OAI.Release075 OAI.Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem OAI.Release075.TriangleFilling.fold {w : List E} (D : TriangleFilling flip color face w)
    (hflip : Function.Involutive flip) (hne : ∀ e, color e ≠ color (flip e))
    {a b : D.Dart} {l : List D.Dart} (hb : D.boundary = b::a::l)
    (hl : D.label a = flip (D.label b)) :
    Nonempty (TriangleFilling flip color face (l.map D.label)) := by sorry
