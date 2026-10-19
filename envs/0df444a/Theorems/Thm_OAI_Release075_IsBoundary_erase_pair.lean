-- Prove2me | Theorems.Thm_OAI_Release075_IsBoundary_erase_pair
-- name    : OAI.Release075.IsBoundary.erase_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:57:50.792622+00:00
-- url     : https://prove2.me/theorems/68d1693e-9ffd-45ab-b187-bbc9c2977390
-- title:
--   Removing two leading darts from a boundary cycle
-- statement:
--   Let $f$ be a permutation of a set and let $b,a,c_1,\dots,c_k$ be distinct elements forming a boundary of $f$, i.e. $f$ acts on them as the cyclic shift $b\mapsto a\mapsto c_1\mapsto\cdots\mapsto c_k\mapsto b$. Then the list $c_1,\dots,c_k$ is a boundary of
--   $$
--   f'=(b\ \ f(a))\,f ,
--   $$
--   and $f'(z)=f(z)$ for every $z$ outside $\{b,a,c_1,\dots,c_k\}$.
--
--   Splicing out $b,a$ shortens the boundary cycle by two.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/TriangleFilling.lean#L125-L157

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
variable {A : Type*}

theorem OAI.Release075.IsBoundary.erase_pair {f : Perm A} {a b : A} {l : List A}
    (h : IsBoundary f (b::a::l)) :
    IsBoundary (Equiv.swap b (f a)*f) l ∧
    (∀ z, z ∉ b::a::l → (Equiv.swap b (f a)*f) z = f z) := by sorry
