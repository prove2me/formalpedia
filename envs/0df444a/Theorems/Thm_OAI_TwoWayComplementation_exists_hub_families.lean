-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_exists_hub_families
-- name    : OAI.TwoWayComplementation.exists_hub_families
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:50:30.100857+00:00
-- url     : https://prove2.me/theorems/24b8a623-94f1-4530-858c-fe7780a24f17
-- title:
--   Two disjoint families of 64 points and a separate hub in any set of at least 129 points
-- statement:
--   Let $H$ be a finite set with $|H|\ge129$. Then there are injective maps $u,v:\{0,\dots,63\}\to H$ and a point $z\in H$ such that
--   $$
--   u(i)\neq v(j),\qquad u(i)\neq z,\qquad v(j)\neq z\qquad\text{for all } i,j\in\{0,\dots,63\}.
--   $$
--
--   In other words, $H$ contains $129$ distinct points arranged as two families of $64$ points and a hub. They form the frame of the amplification step in the complementation lower bound: the left points $u(i)$, the right points $v(j)$ and the hub $z$. The $64^2=4096$ pairs $(u(i),v(j))$ are the edges inserted one by one, and each of them is obtained by composing a pair $(u(i),z)$ with a pair $(z,v(j))$ through the hub.
--
--   **Formalization Note** $|H|$ is `Nat.card H`, finiteness is the instance `Finite H`, and $u,v$ are embeddings `Fin 64 ↪ H`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Retained.lean#L9-L37

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

theorem OAI.TwoWayComplementation.exists_hub_families {H : Type*} [Finite H] (hh : 129 ≤ Nat.card H) :
    ∃ u v : Fin 64 ↪ H, ∃ z : H,
      (∀ i j, u i ≠ v j) ∧ (∀ i, u i ≠ z) ∧ (∀ j, v j ≠ z) := by sorry
