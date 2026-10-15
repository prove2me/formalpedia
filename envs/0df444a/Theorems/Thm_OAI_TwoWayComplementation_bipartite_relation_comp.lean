-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_bipartite_relation_comp
-- name    : OAI.TwoWayComplementation.bipartite_relation_comp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:47:35.077981+00:00
-- url     : https://prove2.me/theorems/cd22f3f9-7220-439a-b49f-94370011381c
-- title:
--   Adding bipartite edges to a partial identity: products of such relations unite their edge sets
-- statement:
--   Let $H$ be a set. Relations on $H$ are composed in path order: $(x,z)\in RS$ if and only if $(x,y)\in R$ and $(y,z)\in S$ for some $y\in H$. For $F\subseteq H$ let $\Delta_F=\{(x,x):x\in F\}$ be the partial identity on $F$.
--
--   **Theorem.** Let $F,U,V\subseteq H$ with $U\subseteq F$, $V\subseteq F$ and $U\cap V=\varnothing$, and let $E,E'\subseteq U\times V$, so that every pair of $E$ or $E'$ leads from a point of $U$ to a point of $V$. Then
--   $$
--   (\Delta_F\cup E)\,(\Delta_F\cup E')=\Delta_F\cup E\cup E' .
--   $$
--
--   Since no pair of $E$ ends where a pair of $E'$ starts, edges cannot be concatenated, and composing two such relations simply merges their edge sets. In particular every relation $\Delta_F\cup E$ with $E\subseteq U\times V$ is idempotent, and any two of them commute. In the amplification step of the complementation lower bound, this identity tracks the image relation $\Delta_F\cup E$ while bipartite edges are inserted one at a time.
--
--   **Formalization Note** $H$ is an arbitrary type, the relations are `SetRel H H` composed with `○`, $\Delta_F$ is `restrictedIdentity F`, and $U\times V$ is `U ×ˢ V`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean#L93-L109

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

theorem OAI.TwoWayComplementation.bipartite_relation_comp {H : Type*} (F U V : Set H)
    (hU : U ⊆ F) (hV : V ⊆ F) (hUV : Disjoint U V)
    (E E' : SetRel H H) (hE : E ⊆ U ×ˢ V) (hE' : E' ⊆ U ×ˢ V) :
    (restrictedIdentity F ∪ E) ○ (restrictedIdentity F ∪ E') =
      restrictedIdentity F ∪ (E ∪ E') := by sorry
