-- Prove2me | Theorems.Thm_OAI_Barnette_TriangleSystem_oppositeGraph_adj_iff
-- name    : OAI.Barnette.TriangleSystem.oppositeGraph_adj_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:25:05.806997+00:00
-- url     : https://prove2.me/theorems/6d3634c9-4b93-4887-8b1b-d654407f3950
-- title:
--   Adjacency in the opposite graph of a state, described through a partner state
-- statement:
--   A *triangle system* on a set $V$, indexed by a set $I$, assigns to each $t\in I$ three distinct corners $\tau_t(0),\tau_t(1),\tau_t(2)\in V$, indices in $\mathbb{Z}/3$, in such a way that two triangles sharing two corners coincide: if $\tau_t(i)=\tau_u(k)$ and $\tau_t(j)=\tau_u(l)$ with $i\neq j$ and $k\neq l$, then $t=u$. For a set $X\subseteq V$, a *state* for $X$ is a choice of a corner index $s_t\in\mathbb{Z}/3$ for every triangle $t$ such that $t\mapsto\tau_t(s_t)$ is a bijection from $I$ onto $X$. Two states $r,s$ for $X$ are *partners* if $\tau_t(r_t)\neq\tau_t(s_t)$ for every $t$. For $i\neq j$ in $\mathbb{Z}/3$ the *third index* is $\theta(i,j)=-(i+j)$, the unique element of $\mathbb{Z}/3$ different from $i$ and $j$.
--
--   The *opposite graph* $O(s)$ of a state $s$ is the simple graph on $V$ in which distinct $v,w$ are adjacent if and only if there are a triangle $t$ and indices $i,j\neq s_t$ with $\tau_t(i)=v$ and $\tau_t(j)=w$; in other words, each triangle contributes the edge joining its two corners not selected by $s$.
--
--   If $r$ and $s$ are partner states for $X$, then for all $v,w\in V$, $v$ and $w$ are adjacent in $O(s)$ if and only if there is a triangle $t$ with
--
--   $$
--   \bigl(v=\tau_t(r_t)\ \text{and}\ w=\tau_t(\theta(r_t,s_t))\bigr)\quad\text{or}\quad\bigl(w=\tau_t(r_t)\ \text{and}\ v=\tau_t(\theta(r_t,s_t))\bigr).
--   $$
--
--   So once a partner $r$ of $s$ is fixed, every edge of $O(s)$ comes with a natural direction, from the corner selected by $r$ to the remaining third corner. This is used to realize the opposite graph as the underlying graph of an oriented network on the dual vertices, one edge per triangle.
--
--   **Formalization Note** In Lean the index type of the triangles is called `A`; it and $V$ are arbitrary types, $X$ is an arbitrary set, and a state is a subtype of maps `c : A → Fin 3`, with $\tau_t(s_t)$ written `s.value t`; $\theta$ is `thirdIndex`. The statement does not use the two-shared-corners axiom or the bijectivity in the definition of a state.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/TriangleSystem.lean#L113-L134

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

open OAI OAI.Barnette OAI.Barnette.TriangleSystem
variable {A V : Type*} (T : TriangleSystem A V)

theorem OAI.Barnette.TriangleSystem.oppositeGraph_adj_iff {X : Set V} {r s : T.State X} (hrs : T.Partner r s)
    (v w : V) : (T.oppositeGraph s).Adj v w ↔
    ∃ t, (v = r.value t ∧ w = T.vertex t (thirdIndex (r.val t) (s.val t))) ∨
      (w = r.value t ∧ v = T.vertex t (thirdIndex (r.val t) (s.val t))) := by sorry
