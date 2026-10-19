-- Prove2me | Theorems.Thm_OAI_Barnette_Network_Duality_vertex_flow_circuit
-- name    : OAI.Barnette.Network.Duality.vertex_flow_circuit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:14:16.516224+00:00
-- url     : https://prove2.me/theorems/457ef828-1f1d-4ad5-9283-0de90e032373
-- title:
--   The star of a non-separating dual vertex is a minimal circulation
-- statement:
--   Let $N$ and $D$ be networks on a common finite edge set $E$ with vertex sets $V$ and $F$: every edge $e$ has a tail and a head, $t_N(e),h_N(e)\in V$ in $N$ and $t_D(e),h_D(e)\in F$ in $D$. The gradient of $f:F\to\mathbb{R}$ in $D$ is $(\nabla_D f)(e)=f(h_D(e))-f(t_D(e))$, and the boundary of $x:E\to\mathbb{R}$ in $N$ is $(\partial_N x)(v)=\sum_{e:\,h_N(e)=v}x(e)-\sum_{e:\,t_N(e)=v}x(e)$; $\nabla_N$ and $\partial_D$ are defined in the same way. The underlying graph $G(D)$ is the simple graph on $F$ in which distinct vertices are adjacent when some edge joins them, and similarly for $G(N)$. The networks are *dual* if $G(N)$ and $G(D)$ are connected, $\ker\partial_N=\operatorname{im}\nabla_D$ and $\ker\partial_D=\operatorname{im}\nabla_N$.
--
--   The support of $x:E\to\mathbb{R}$ is $\operatorname{supp}x=\{e: x(e)\neq0\}$. A *flow circuit* of $N$ is a function $x:E\to\mathbb{R}$ such that $\partial_N x=0$, $x\neq0$, and every $y$ with $\partial_N y=0$ and $\operatorname{supp}y\subseteq\operatorname{supp}x$ satisfies $y=0$ or $\operatorname{supp}y=\operatorname{supp}x$.
--
--   Assume $N$ and $D$ are dual, and let $z\in F$ be a vertex such that the subgraph of $G(D)$ induced on $F\setminus\{z\}$ is connected. Then the gradient of the indicator of $z$,
--
--   $$
--   x_z=\nabla_D\mathbf 1_z,\qquad x_z(e)=[h_D(e)=z]-[t_D(e)=z],
--   $$
--
--   is a flow circuit of $N$. Here $[P]$ is $1$ if $P$ holds and $0$ otherwise.
--
--   The support of $x_z$ consists of the non-loop edges of $D$ at $z$, each signed according to whether it enters or leaves $z$. In the planar picture, where $z$ is a face of the plane graph $N$, this says that the boundary of a face whose removal does not disconnect the dual is a single circuit of $N$. It is used to show that a dual vertex lying in the regions of both a vertex set $A$ and its complement must touch an edge of the cut of $A$.
--
--   **Formalization Note** Neither $V$ nor $F$ is required to be finite; the indicator is `fun w => if w = z then 1 else 0`. Since connectedness in Mathlib includes nonemptiness, the hypothesis forces $F$ to contain a vertex other than $z$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/StateDisk.lean#L17-L77

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
theorem OAI.Barnette.Network.Duality.vertex_flow_circuit (h : N.Duality D) (z : F)
    (hz : (D.graph.induce {v | v ≠ z}).Connected) :
    N.FlowCircuit (D.gradient (fun w => if w = z then 1 else 0)) := by sorry
