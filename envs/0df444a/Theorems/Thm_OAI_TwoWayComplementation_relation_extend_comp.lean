-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_relation_extend_comp
-- name    : OAI.TwoWayComplementation.relation_extend_comp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:44:27.887685+00:00
-- url     : https://prove2.me/theorems/b68adec0-ad54-469f-8b81-0a0200277103
-- title:
--   Extending relations from a subset to the ambient set preserves composition
-- statement:
--   Let $H$ be a set and $F\subseteq H$ a subset. Relations are composed in path order, $XY=\{(x,z):\exists y\ (x,y)\in X,\ (y,z)\in Y\}$. For a relation $A$ on $F$ let
--   $$
--   \widehat A=\{(x,y)\in H\times H:\ x\in F,\ y\in F,\ (x,y)\in A\}
--   $$
--   be its extension to $H$, i.e. the image of $A$ under the inclusion $F\times F\hookrightarrow H\times H$.
--
--   **Theorem.** For all relations $A,B$ on $F$,
--   $$
--   \widehat{AB}=\widehat A\,\widehat B ,
--   $$
--   where $AB$ is composed in $F$ and $\widehat A\,\widehat B$ in $H$.
--
--   Thus extension is a multiplicative embedding of the relation monoid of $F$ into that of $H$; it sends the identity relation of $F$ to the partial identity $\Delta_F=\{(x,x):x\in F\}$ rather than to the identity of $H$. This multiplicativity is what makes the bijection between the full relation monoid on $F$ and a corner of the relation monoid on $H$ (extension followed by sandwiching with an idempotent relation) a monoid isomorphism.
--
--   **Formalization Note** $A$ and $B$ are relations on the subtype `F`, and the extension is the image under `Prod.map Subtype.val Subtype.val`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean#L139-L155

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.relation_extend_comp {H : Type*} (F : Set H) (A B : SetRel F F) :
    (Prod.map Subtype.val Subtype.val) '' (A ○ B) =
      ((Prod.map Subtype.val Subtype.val) '' A) ○
        ((Prod.map Subtype.val Subtype.val) '' B) := by sorry
