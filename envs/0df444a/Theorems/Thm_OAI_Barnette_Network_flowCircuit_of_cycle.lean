-- Prove2me | Theorems.Thm_OAI_Barnette_Network_flowCircuit_of_cycle
-- name    : OAI.Barnette.Network.flowCircuit_of_cycle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:07:26.333479+00:00
-- url     : https://prove2.me/theorems/348870f8-0fc8-4f7b-8c8e-e25c62dd69a4
-- title:
--   A circulation supported exactly on a cycle is a flow circuit
-- statement:
--   A *network* $N$ with vertex set $V$ and finite edge set $E$ is a pair of maps $\mathrm{tail},\mathrm{head}:E\to V$. Its underlying graph $G(N)$ joins distinct $v,w$ iff some edge has endpoint pair $\{v,w\}$. The network is *simple* if $\mathrm{tail}(e)\ne\mathrm{head}(e)$ for all $e$ and distinct edges have distinct endpoint pairs. The boundary of $x:E\to\mathbb{R}$ is $(\partial_N x)(v)=\sum_{\mathrm{head}(e)=v}x_e-\sum_{\mathrm{tail}(e)=v}x_e$; $x$ is a *circulation* if $\partial_N x=0$, and $\operatorname{supp}x=\{e:\ x_e\ne0\}$. A *flow circuit* of $N$ is a circulation $x\ne0$ such that every circulation $y$ with $\operatorname{supp}y\subseteq\operatorname{supp}x$ satisfies $y=0$ or $\operatorname{supp}y=\operatorname{supp}x$.
--
--   A cycle $C$ of $G(N)$ is given in coordinates by a length $L=n+3$ (with $n\in\mathbb{N}$, so $L\ge3$) and an injective map $i\mapsto u_i$ from $\mathbb{Z}/L\mathbb{Z}$ to $V$ such that $u_i$ and $u_{i+1}$ are adjacent in $G(N)$ for every $i$. For each $i$ fix, once and for all, an edge $e_i$ of $N$ with endpoint pair $\{u_i,u_{i+1}\}$, and let $Z(C)=\{e_0,\dots,e_{L-1}\}$ be the edge set of the cycle.
--
--   **Theorem.** Let $N$ be simple and $C$ a cycle of $G(N)$ as above. If $x$ is a circulation of $N$ whose support is exactly the edge set of the cycle, then $x$ is a flow circuit:
--
--   $$\partial_N x=0\ \text{ and }\ \operatorname{supp}x=Z(C)\quad\Longrightarrow\quad x\ \text{is a flow circuit of } N.$$
--
--   So cycles of the underlying graph give rise to flow circuits; together with the description of flow circuits of a dual network as cuts, this links cycles on one side of a duality to bonds on the other.
--
--   **Formalization Note** The vertex type $V$ need not be finite. The cycle is a `CycleCoordinates N.graph` with fields `n`, `vertex : Fin (n+3) ↪ V` and `adjacent`; the edges $e_i$ are `N.cycleEdge C i`, chosen with `Exists.choose`, and $Z(C)$ is `N.cycleEdges C`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/FlowCircuits.lean#L341-L355

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

omit [Fintype V] in
theorem OAI.Barnette.Network.flowCircuit_of_cycle (hN : N.Simple) (x : E → ℝ)
    (hx : N.boundary x = 0) (hs : N.flowSupport x = N.cycleEdges C) : N.FlowCircuit x := by sorry
