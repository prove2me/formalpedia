-- Prove2me | Theorems.Thm_OAI_Release075_PermCycles_components_conjugate_swap
-- name    : OAI.Release075.PermCycles.components_conjugate_swap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:51:23.802621+00:00
-- url     : https://prove2.me/theorems/75778823-ae81-4091-b5ed-35f7bdce1aeb
-- title:
--   Re-pairing two slots of one component splits off at most one component
-- statement:
--   Let $f,g$ be permutations of a finite set and $a,b$ two elements in the same component of $\langle f,g\rangle$. Let $f'=(a\ b)\,f\,(a\ b)$. Then the components of $\langle f,g\rangle$ are obtained from those of $\langle f',g\rangle$ by joining the classes of $a$ and $b$:
--   $$
--   \mathrm{comp}(f,g)=\mathrm{join}_{a,b}\bigl(\mathrm{comp}(f',g)\bigr).
--   $$
--
--   So re-pairing can split the component into at most two.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Planarity.lean#L58-L79

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity

open OAI OAI.Release075 OAI.Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem OAI.Release075.PermCycles.components_conjugate_swap (f g : Perm A) {a b : A}
    (hab : components f g a b) :
    components f g = joinPair (components (Equiv.swap a b * f * Equiv.swap a b) g) a b := by sorry
