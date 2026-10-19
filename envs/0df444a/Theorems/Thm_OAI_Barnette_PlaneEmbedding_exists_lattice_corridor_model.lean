-- Prove2me | Theorems.Thm_OAI_Barnette_PlaneEmbedding_exists_lattice_corridor_model
-- name    : OAI.Barnette.PlaneEmbedding.exists_lattice_corridor_model
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:16:09.477046+00:00
-- url     : https://prove2.me/theorems/f4ddd86f-9f1a-4291-87da-b26b96519755
-- title:
--   Every finite plane graph has a model by disjoint connected vertex regions and corridors in the square grid
-- statement:
--   Let $G$ be a simple graph on a vertex set $V$ and $H$ a simple graph on a vertex set $W$. A *dart* of $G$ is an ordered pair $d=(a,b)$ of adjacent vertices; its underlying edge is $\{a,b\}$. A *corridor model of $G$ in $H$* consists of sets $B_v\subseteq W$ for $v\in V$ (branch sets) and $C_d\subseteq W$ for darts $d$ of $G$ (corridors) such that
--   1. every $B_v$ and every $C_d$ is finite and induces a connected subgraph of $H$;
--   2. $B_v\cap B_w=\varnothing$ whenever $v\neq w$;
--   3. $C_d\cap C_e=\varnothing$ whenever $d$ and $e$ have different underlying edges;
--   4. $B_v\cap C_d=\varnothing$ whenever $v$ is neither endpoint of $d$;
--   5. for every dart $d=(a,b)$, both $B_a\cap C_d$ and $B_b\cap C_d$ are nonempty.
--
--   A plane embedding of $G$ places the vertices at distinct points of $\mathbb{R}^2$ and joins adjacent vertices by injective continuous arcs that pass through no other vertex point, reverse when the edge is traversed backwards, and have pairwise disjoint interiors for distinct edges. Let $\Gamma$ be the square grid graph on $\mathbb{Z}^2$, in which $z$ and $z'$ are adjacent when they agree in one coordinate and differ by exactly $1$ in the other.
--
--   **Theorem.** Let $V$ be finite and suppose $G$ has a plane embedding. Then
--
--   $$
--   G\ \text{has a corridor model in the square grid graph}\ \Gamma\ \text{on}\ \mathbb{Z}^2 .
--   $$
--
--   This is the bridge from the topological definition of planarity to a purely combinatorial one: each vertex becomes a finite connected lattice region and each edge a finite connected corridor touching exactly the regions of its endpoints among all vertex regions. The corridor model is subsequently turned into a minor model, exhibiting $G$ as a minor of the square grid.
--
--   **Formalization Note** The conclusion is `Nonempty (CorridorModel G SquareGrid.graph)` with the embedding `E : PlaneEmbedding G` as hypothesis; `V` carries a `Fintype` instance and adjacency is decidable (`DecidableRel G.Adj`), which makes the set of darts finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Corridors.lean#L58-L90

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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_SquareGrid
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Corridors

open OAI OAI.Barnette OAI.Barnette.PlaneEmbedding
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] (E : PlaneEmbedding G)

omit [DecidableEq V] in
include E in
theorem OAI.Barnette.PlaneEmbedding.exists_lattice_corridor_model : Nonempty (CorridorModel G SquareGrid.graph) := by sorry
