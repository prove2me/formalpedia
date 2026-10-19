-- Prove2me | Theorems.Thm_OAI_Barnette_Network_addSink_acyclic
-- name    : OAI.Barnette.Network.addSink_acyclic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:50:02.715456+00:00
-- url     : https://prove2.me/theorems/4ee68da5-0beb-4f9f-a935-a30e3f2e1630
-- title:
--   Adding two arcs into a fresh sink keeps a tail-injective forest acyclic
-- statement:
--   Let $Q$ be an oriented network with vertex set $V$ and edge set $A$ (no finiteness is assumed): every edge $a$ has a tail $\operatorname{tail}(a)\in V$ and a head $\operatorname{head}(a)\in V$. Its underlying simple graph $G_Q$ joins two distinct vertices $x,y$ when some edge has endpoints $\{x,y\}$. Given an injective map $j\mapsto r_j$ from $\{0,1\}$ to $V$ and a vertex $z\in V$, let $Q^{+}$ be the network on $V$ with edge set $A\sqcup\{0,1\}$ which keeps every edge of $Q$ and adds, for $j=0,1$, a new edge with tail $r_j$ and head $z$.
--
--   Assume:
--
--   1. $G_Q$ is acyclic;
--   2. the tail map of $Q$ is injective, i.e. every vertex is the tail of at most one edge of $Q$;
--   3. no edge of $Q$ has its tail at $r_0$ or at $r_1$;
--   4. $z$ is not the tail of any edge of $Q^{+}$, i.e. $z$ is not the tail of an edge of $Q$ and $z\notin\{r_0,r_1\}$.
--
--   Then
--
--   $$G_{Q^{+}}\ \text{is acyclic}.$$
--
--   In the recovery of Hamiltonian cycles from corner states, forests on the dual vertex set are encoded as networks in which every black vertex contributes one arc leaving the corner it selects, so tails are distinct; the two edges of the root triangle are then attached as two arcs into a third root corner. This lemma shows that such an attachment cannot create a cycle.
--
--   **Formalization Note** The augmented network is `Q.addSink r z` with edge type `A ⊕ Fin 2`, tail map `Sum.elim Q.tail r` and head map `Sum.elim Q.head (fun _ => z)`; hypothesis 4 is stated as `z ∉ Set.range (Q.addSink r z).tail`. Acyclicity is Mathlib's `SimpleGraph.IsAcyclic` for the underlying simple graph `Q.graph`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Matching.lean#L114-L149

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V A : Type*} (Q : Network V A)

theorem OAI.Barnette.Network.addSink_acyclic (ha : Q.graph.IsAcyclic) (ht : Function.Injective Q.tail)
    (r : Fin 2 → V) (hr : Function.Injective r) (hd : ∀ a i, Q.tail a ≠ r i)
    (z : V) (hz : z ∉ Set.range (Q.addSink r z).tail) : (Q.addSink r z).graph.IsAcyclic := by sorry
