-- Prove2me | Theorems.Thm_OAI_Barnette_Network_boundary_of_sum_zero
-- name    : OAI.Barnette.Network.boundary_of_sum_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:20:52.037864+00:00
-- url     : https://prove2.me/theorems/1d7f0b1b-063a-4622-9eaf-384ee86b173b
-- title:
--   On a connected network every zero-sum vertex function is a boundary
-- statement:
--   Let $N$ be a network with finite vertex set $V$ and finite edge set $E$, each edge $e$ having a tail $t(e)$ and a head $h(e)$ in $V$. The boundary of an edge function $x:E\to\mathbb{R}$ is the vertex function
--   $$
--   (\partial_N x)(v)=\sum_{e:\,h(e)=v}x(e)-\sum_{e:\,t(e)=v}x(e),
--   $$
--   the net inflow at $v$. Let $G(N)$ be the underlying simple graph (distinct vertices adjacent when some edge joins them).
--
--   If $G(N)$ is connected and $b:V\to\mathbb{R}$ satisfies $\sum_{v\in V}b(v)=0$, then there is an edge function $x$ with prescribed boundary $b$:
--
--   $$
--   \sum_{v\in V}b(v)=0\quad\Longrightarrow\quad \exists\,x:E\to\mathbb{R}\ \text{ with }\ \partial_N x=b .
--   $$
--
--   Since every boundary has total sum zero, this identifies the image of $\partial_N$ with the hyperplane of zero-sum functions whenever $G(N)$ is connected. It is used to produce a flow whose net inflow is a prescribed charge distribution, such as one unit at every white vertex balanced by a single sink at a root.
--
--   **Formalization Note** The boundary is the linear map `N.boundary`, given by the signed incidence matrix of $N$; connectivity is `N.graph.Connected`, which includes nonemptiness of $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Circulation.lean#L154-L181

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

theorem OAI.Barnette.Network.boundary_of_sum_zero (h : N.graph.Connected) (b : V → ℝ)
    (hb : ∑ v, b v = 0) : ∃ x, N.boundary x = b := by sorry
