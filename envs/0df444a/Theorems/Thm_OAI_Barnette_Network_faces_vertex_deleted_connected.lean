-- Prove2me | Theorems.Thm_OAI_Barnette_Network_faces_vertex_deleted_connected
-- name    : OAI.Barnette.Network.faces_vertex_deleted_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:09:54.597921+00:00
-- url     : https://prove2.me/theorems/e592679f-596b-4c55-ba8b-f1ba0a10214e
-- title:
--   A dual network whose vertex stars are triangles stays connected after deleting any vertex
-- statement:
--   Let $E$ be a finite set and let $N$ and $D$ be networks with vertex sets $V$ and $F$ and the common edge set $E$; a network is a pair of maps $\mathrm{tail},\mathrm{head}$ from $E$ to its vertex set. An edge $e$ is incident to a vertex $p$ if $p$ is one of its two endpoints. The underlying graph $G(\cdot)$ of a network joins distinct vertices $p,p'$ iff some edge has endpoint pair $\{p,p'\}$. $D$ is *simple* if it has no loops ($\mathrm{tail}_D(e)\ne\mathrm{head}_D(e)$) and distinct edges have distinct endpoint pairs in $D$. The *star* of $v\in V$ in $N$ is $\operatorname{star}_N(v)=\{e\in E:\ e \text{ is incident to } v \text{ in } N\}$. A *triangle* of $D$ on a set $s\subseteq E$ consists of three distinct vertices $c_0,c_1,c_2\in F$ and three distinct edges $e_0,e_1,e_2$ with $\{e_0,e_1,e_2\}=s$ such that the endpoint pair of $e_i$ in $D$ is $\{c_i,c_{i+1}\}$, indices modulo $3$.
--
--   **Theorem.** Assume that $G(N)$ and $G(D)$ are connected, that $D$ is simple, and that for every vertex $v\in V$ the star $\operatorname{star}_N(v)$ carries a triangle of $D$. Then for every $z\in F$ the graph obtained from $G(D)$ by deleting $z$ is connected:
--
--   $$G(D)-z\;=\;G(D)\big[F\setminus\{z\}\big]\quad\text{is connected.}$$
--
--   The hypothesis says that the edges at each vertex of $N$ form a triangle in $D$, as happens when $D$ is a dual of a cubic plane network $N$, each vertex of $N$ corresponding to a triangular face of $D$. The conclusion says that such a $D$ has no cut vertex; in particular $F\setminus\{z\}$ is nonempty, since a connected graph has at least one vertex.
--
--   **Formalization Note** The hypothesis on stars is a family `face : ∀ v, D.Triangle (N.star v)`, and $G(D)-z$ is `D.graph.induce {v | v ≠ z}`. The vertex sets $V$ and $F$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Bonds.lean#L263-L300

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

omit [Fintype V] [Fintype F] in
theorem OAI.Barnette.Network.faces_vertex_deleted_connected (hN : N.graph.Connected) (hD : D.graph.Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) (z : F) :
    (D.graph.induce {v | v ≠ z}).Connected := by sorry
