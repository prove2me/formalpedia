-- Prove2me | Theorems.Thm_OAI_Barnette_Network_Bond_connected_shore
-- name    : OAI.Barnette.Network.Bond.connected_shore
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:09:03.085461+00:00
-- url     : https://prove2.me/theorems/bbe3ae34-d6ee-4336-a6ac-70ec1cef7207
-- title:
--   A nonempty proper shore of a bond in a connected network induces a connected subgraph
-- statement:
--   A *network* with vertex set $X$ and finite edge set $E$ is a pair of maps $\mathrm{tail},\mathrm{head}:E\to X$. For a network $N$ with vertex set $V$ and a finite set $A\subseteq V$, the *cut* $\delta_N(A)$ is the set of edges with exactly one endpoint in $A$. A finite set $A\subseteq V$ is a *bond* of $N$ if its cut is a minimal nonempty cut:
--
--   $$\delta_N(A)\ne\varnothing\quad\text{and}\quad\text{for every finite } B\subseteq V:\ \ \delta_N(B)\subseteq\delta_N(A)\ \Longrightarrow\ \delta_N(B)=\varnothing\ \text{ or }\ \delta_N(B)=\delta_N(A).$$
--
--   The underlying graph $G(N)$ is the simple graph on $V$ in which distinct $v,w$ are adjacent iff some edge has endpoint pair $\{v,w\}$, and $G(N)[A]$ denotes its subgraph induced on $A$.
--
--   **Theorem.** Let $G(N)$ be connected and let $A$ be a bond of $N$ with $A\ne\varnothing$ and $A\ne V$. Then
--
--   $$G(N)[A]\ \text{ is connected.}$$
--
--   This is the network form of the classical fact that a minimal edge cut of a connected graph has connected shores: if the shore $A$ fell apart, the cut of a single component would be a smaller nonempty cut.
--
--   **Formalization Note** $A$ is a `Finset V`, the hypothesis $A\ne V$ is stated as `∃ v, v ∉ A`, and the induced subgraph is `N.graph.induce {v | v ∈ A}`. The vertex type $V$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Bonds.lean#L161-L198

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
theorem OAI.Barnette.Network.Bond.connected_shore (h : N.graph.Connected) {A : Finset V} (hA : N.Bond A)
    (hin : A.Nonempty) (hout : ∃ v, v ∉ A) :
    (N.graph.induce {v | v ∈ A}).Connected := by sorry
