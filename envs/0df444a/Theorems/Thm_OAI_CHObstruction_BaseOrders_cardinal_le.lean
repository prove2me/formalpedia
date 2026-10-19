-- Prove2me | Theorems.Thm_OAI_CHObstruction_BaseOrders_cardinal_le
-- name    : OAI.CHObstruction.BaseOrders.cardinal_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:58:58.832009+00:00
-- url     : https://prove2.me/theorems/6619a0b8-7615-4cf5-a861-e20997942c76
-- title:
--   A nonempty locally countable linear order has at most $\aleph_1$ elements
-- statement:
--   Let $(B,\le)$ be a nonempty linearly ordered set which is *locally countable*: every closed interval
--   $[a,b]=\{x\in B:\ a\le x\le b\}$ with $a,b\in B$ is countable (finite or countably infinite). Then
--
--   $$
--   |B|\le\aleph_1 .
--   $$
--
--   The base orders of the arrays in the categoricity construction are required to be locally countable, and this lemma bounds every such base by $\aleph_1$. It keeps the number of functions from a base into the palette, a set of size $2^{\aleph_0}$, at most $(2^{\aleph_0})^{\aleph_1}=2^{\aleph_1}$, which is what the tail bound on index sets needs.
--
--   **Formalization Note** The hypotheses are a `LinearOrder` on the type $B$, `[Nonempty B]` and `∀ a b : B, (Set.Icc a b).Countable`; the conclusion is `#B ≤ ℵ_ 1` in the universe of $B$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/TailBound.lean#L171-L207

import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound

open OAI OAI.CHObstruction
universe u v w
open Cardinal Ordinal Order
variable {B : Type u} [LinearOrder B]

theorem OAI.CHObstruction.BaseOrders.cardinal_le [Nonempty B] (h : ∀ a b : B, (Set.Icc a b).Countable) :
    #B ≤ (ℵ_ 1 : Cardinal.{u}) := by sorry
