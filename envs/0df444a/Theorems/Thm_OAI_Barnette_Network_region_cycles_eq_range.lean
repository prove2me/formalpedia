-- Prove2me | Theorems.Thm_OAI_Barnette_Network_region_cycles_eq_range
-- name    : OAI.Barnette.Network.region_cycles_eq_range
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:12:29.282585+00:00
-- url     : https://prove2.me/theorems/63985c90-43bb-4aec-904c-f6ca156b8bc2
-- title:
--   Circulations of a dual region are restricted gradients of functions on the enclosed vertices
-- statement:
--   Let $N$ and $D$ be networks on a common finite edge set $E$, with vertex sets $V$ and $F$ respectively ($F$ finite): every edge $e$ has a tail and a head, $t_N(e),h_N(e)\in V$ in $N$ and $t_D(e),h_D(e)\in F$ in $D$. For a network $N$ the gradient of $f:V\to\mathbb{R}$ and the boundary of $x:E\to\mathbb{R}$ are
--   $(\nabla_N f)(e)=f(h_N(e))-f(t_N(e))$ and $(\partial_N x)(v)=\sum_{e:\,h_N(e)=v}x(e)-\sum_{e:\,t_N(e)=v}x(e)$, and similarly for $D$ and for any other network. The underlying graph $G(N)$ is the simple graph on $V$ in which two distinct vertices are adjacent when some edge joins them. The networks $N$ and $D$ are *dual* if $G(N)$ and $G(D)$ are connected, $\ker\partial_N=\operatorname{im}\nabla_D$ and $\ker\partial_D=\operatorname{im}\nabla_N$.
--
--   For a finite set $A\subseteq V$ let $E_A$ be the set of edges with at least one $N$-endpoint in $A$, let $F_A$ be the set of vertices of $D$ incident in $D$ to an edge of $E_A$, and let $R_A$ be the network with vertex set $F_A$ and edge set $E_A$ in which each edge keeps its $D$-tail and $D$-head. Define the linear map $\Phi_A:\mathbb{R}^A\to\mathbb{R}^{E_A}$ by $\Phi_A(f)=(\nabla_N\bar f)|_{E_A}$, where $\bar f:V\to\mathbb{R}$ extends $f$ by zero outside $A$.
--
--   If $N$ and $D$ are dual and the subgraph of $G(N)$ induced on $V\setminus A$ is connected, then
--
--   $$
--   \ker\partial_{R_A}=\operatorname{im}\Phi_A .
--   $$
--
--   In words: the circulations of the dual region $R_A$ are exactly the restrictions to $E_A$ of gradients of functions supported on $A$. Since $\Phi_A$ is injective whenever $G(N)$ is connected and $V\setminus A$ is nonempty, this identifies the cycle space of $R_A$ with $\mathbb{R}^A$ and gives $\dim\ker\partial_{R_A}=|A|$, which is the input for the Euler-type count $|A|+|F_A|=|E_A|+1$ of dual regions.
--
--   **Formalization Note** $\Phi_A$ is `N.regionCycleMap A`, built from the extension-by-zero map `push` and the restriction map `pull`, and $\partial_{R_A}$ is `(N.region D A).boundary`. Connectedness of the induced graph includes nonemptiness, so the hypothesis implies $A\neq V$. The vertex type $V$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/DiskRegions.lean#L184-L238

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
theorem OAI.Barnette.Network.region_cycles_eq_range (h : N.Duality D) (A : Finset V)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected) :
    (N.region D A).boundary.ker = (N.regionCycleMap A).range := by sorry
