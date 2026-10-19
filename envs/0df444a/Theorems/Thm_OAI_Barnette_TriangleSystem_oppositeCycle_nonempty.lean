-- Prove2me | Theorems.Thm_OAI_Barnette_TriangleSystem_oppositeCycle_nonempty
-- name    : OAI.Barnette.TriangleSystem.oppositeCycle_nonempty
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:28:34.429982+00:00
-- url     : https://prove2.me/theorems/bdfb3d6a-5609-4861-ada2-5ff81271cc70
-- title:
--   A cycle in the opposite graph of a state runs through distinct triangles
-- statement:
--   **Triangle systems and states.** A triangle system on a vertex set $V$ with index set $A$ assigns to every $t\in A$ an injective labeling $\tau_t:\mathbb{Z}/3\to V$ of the corners of a triangle, such that two triangles sharing two corners coincide: if $\tau_t(a)=\tau_u(a')$ and $\tau_t(b)=\tau_u(b')$ with $a\ne b$ and $a'\ne b'$, then $t=u$. For $X\subseteq V$, a state on $X$ is a map $s:A\to\mathbb{Z}/3$ such that $t\mapsto\tau_t(s(t))$ is injective with image $X$; it selects one corner of every triangle. The opposite graph $G_s$ of $s$ is the simple graph on $V$ in which distinct vertices $v,w$ are adjacent if and only if there are $t\in A$ and $a,b\in\mathbb{Z}/3$ with $\tau_t(a)=v$, $\tau_t(b)=w$, $a\ne s(t)$ and $b\ne s(t)$. Thus every triangle contributes the side opposite to its selected corner.
--
--   **Opposite cycles.** An opposite cycle of $s$ consists of a cycle $z_0,\dots,z_{m-1}$ of $G_s$ ($m\ge3$, distinct vertices, $z_k$ adjacent to $z_{k+1}$ in $G_s$, indices modulo $m$), an injective map $f:\mathbb{Z}/m\to A$ and corner labels $l_k,r_k\in\mathbb{Z}/3$ such that for every $k\in\mathbb{Z}/m$
--
--   $$\tau_{f(k)}(l_k)=z_k,\qquad\tau_{f(k)}(r_k)=z_{k+1},\qquad l_k\ne s(f(k)),\qquad r_k\ne s(f(k)).$$
--
--   **Theorem.** Let $s$ be a state on $X$. If $G_s$ is not acyclic, then $s$ has an opposite cycle.
--
--   The essential content is the injectivity of $f$: different edges of the cycle are witnessed by different triangles. This allows a state to be modified triangle by triangle along the cycle, which is how the reversal involution on the partners of a state is built.
--
--   **Formalization Note** The triangle system is `T : TriangleSystem A V` (fields `vertex`, `vertex_injective`, `edge_unique`), states are `T.State X`, the opposite graph is `T.oppositeGraph s`, and an opposite cycle is `T.OppositeCycle s` with fields `cycle : CycleCoordinates (T.oppositeGraph s)`, `face` (an embedding), `leftCorner` and `rightCorner`. No finiteness is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/CycleReversal.lean#L48-L74

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

open OAI OAI.Barnette OAI.Barnette.TriangleSystem
open Fin.NatCast
variable {V : Type*} {G : SimpleGraph V}
variable {A : Type*} (T : TriangleSystem A V) {X : Set V}

theorem OAI.Barnette.TriangleSystem.oppositeCycle_nonempty (s : T.State X) (hc : ¬(T.oppositeGraph s).IsAcyclic) :
    Nonempty (T.OppositeCycle s) := by sorry
