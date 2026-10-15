-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_permutation_single_entrance
-- name    : OAI.OneWayLiveness.permutation_single_entrance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:11:10.246254+00:00
-- url     : https://prove2.me/theorems/5738abe0-8e93-4699-a65a-9f06e61bbf3e
-- title:
--   A permutation orbit that leaves a set can only return through its single entrance
-- statement:
--   Let $D$ be a finite set, $\tau$ a permutation of $D$, and $U\subseteq D$. Call $d\in D$ an *entrance* of $U$ if $d\notin U$ and $\tau(d)\in U$. Suppose that $a\in U$ satisfies $\tau(a)\notin U$, and that $b\in D$ is such that every entrance of $U$ equals $b$. Then $a$ and $b$ lie in the same cycle of $\tau$:
--   $$
--   \exists\,k\in\mathbb{Z}:\qquad \tau^{k}(a)=b .
--   $$
--
--   Intuitively, the orbit of $a$ leaves $U$ at once, and since it is a finite cycle it must come back to $a\in U$. It can only re-enter $U$ through an entrance, and the only possible entrance is $b$. The lemma is the combinatorial core of a face-tracing argument for rotation systems: it shows that both darts of an edge lie on the same tour when the edge leads towards a terminal vertex.
--
--   **Formalization Note** The conclusion is `Equiv.Perm.SameCycle τ a b`, and finiteness of $D$ is the instance `Finite D`. It is not assumed that $b$ is actually an entrance of $U$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Tours.lean#L7-L23

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours

open OAI OAI.OneWayLiveness

theorem OAI.OneWayLiveness.permutation_single_entrance {D : Type*} [Finite D] (τ : Equiv.Perm D)
    (U : Set D) (a b : D) (ha : a ∈ U) (ha' : τ a ∉ U)
    (hin : ∀ d, d ∉ U → τ d ∈ U → d = b) : τ.SameCycle a b := by sorry
