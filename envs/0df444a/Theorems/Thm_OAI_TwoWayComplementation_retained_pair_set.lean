-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_retained_pair_set
-- name    : OAI.TwoWayComplementation.retained_pair_set
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:51:05.614994+00:00
-- url     : https://prove2.me/theorems/6220ca09-046a-4c5f-82f4-b9d96bbcf4b7
-- title:
--   Keeping one point of each 64-point family and deleting the hub removes exactly 127 points
-- statement:
--   Let $H$ be a finite set, let $U,V\subseteq H$ be disjoint with $|U|=|V|=64$, and let $z\in H\setminus(U\cup V)$, $x\in U$ and $y\in V$. Then there is a set $F\subseteq H$ with
--   $$
--   |F|=|H|-127,\qquad x,y\in F,\qquad z\notin F,\qquad F\cap U=\{x\},\qquad F\cap V=\{y\} .
--   $$
--
--   Such an $F$ is obtained by deleting from $H$ the hub $z$ and all points of $U\cup V$ other than $x$ and $y$. In the amplification step of the complementation lower bound, $F$ is the retained label set for the edge $(x,y)$. Restricted to $F$, the relation built from the earlier edges is the identity, while the edge $(x,y)$ survives, so the argument can be restarted on a label set with $127$ fewer points.
--
--   **Formalization Note** The cardinality of $F$ is `Nat.card F` for the subtype $F$, and $|H|-127$ is natural-number subtraction; it is a genuine difference because $U$, $V$ and $z$ already provide $129$ distinct points of $H$. The conditions $F\cap U=\{x\}$ and $F\cap V=\{y\}$ are stated as: every $a\in U$ with $a\in F$ equals $x$, and every $b\in V$ with $b\in F$ equals $y$; together with $x,y\in F$ they are equivalent to the displayed equalities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Retained.lean#L39-L76

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.retained_pair_set {H : Type*} [Finite H] (U V : Set H)
    (hU : U.ncard = 64) (hV : V.ncard = 64) (hUV : Disjoint U V)
    (z x y : H) (hzU : z ∉ U) (hzV : z ∉ V) (hx : x ∈ U) (hy : y ∈ V) :
    ∃ F : Set H, Nat.card F = Nat.card H - 127 ∧ x ∈ F ∧ y ∈ F ∧ z ∉ F ∧
      (∀ a ∈ U, a ∈ F → a = x) ∧ (∀ b ∈ V, b ∈ F → b = y) := by sorry
