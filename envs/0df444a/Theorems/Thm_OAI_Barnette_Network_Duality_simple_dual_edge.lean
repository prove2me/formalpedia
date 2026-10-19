-- Prove2me | Theorems.Thm_OAI_Barnette_Network_Duality_simple_dual_edge
-- name    : OAI.Barnette.Network.Duality.simple_dual_edge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:54:39.176982+00:00
-- url     : https://prove2.me/theorems/f4bb28d5-0af0-4683-a9e9-c8a7d6a63dbc
-- title:
--   The dual of a three-edge-connected network is simple
-- statement:
--   Let $N$ and $D$ be oriented networks on a common finite edge set $E$, with finite vertex set $V$ for $N$ and vertex set $F$ for $D$; every edge has a tail and a head in each network. The underlying simple graph of a network joins two distinct vertices when some edge has exactly these endpoints. Let $\nabla_N:\mathbb{R}^V\to\mathbb{R}^E$, $(\nabla_N f)(e)=f(\operatorname{head}(e))-f(\operatorname{tail}(e))$, and $\partial_N:\mathbb{R}^E\to\mathbb{R}^V$, $(\partial_N x)(v)=\sum_{\operatorname{head}(e)=v}x_e-\sum_{\operatorname{tail}(e)=v}x_e$, be the gradient and boundary maps of $N$, and similarly $\nabla_D,\partial_D$. Assume that $N$ and $D$ are *dual*: both underlying simple graphs are connected, $\ker\partial_N=\operatorname{im}\nabla_D$ and $\ker\partial_D=\operatorname{im}\nabla_N$. Assume also that $N$ is *three-edge-connected*: for every $A\subseteq V$ with $A\neq\emptyset$ and $V\setminus A\neq\emptyset$, at least three edges have exactly one endpoint in $A$.
--
--   Then $D$ is simple: it has no loops and no two distinct edges with the same unordered pair of endpoints,
--
--   $$\operatorname{tail}_D(e)\neq\operatorname{head}_D(e)\ \ \forall e,\qquad \{\operatorname{tail}_D(e),\operatorname{head}_D(e)\}=\{\operatorname{tail}_D(f),\operatorname{head}_D(f)\}\implies e=f.$$
--
--   This is the algebraic form of the familiar fact that a loop of the planar dual corresponds to a bridge and a pair of parallel dual edges to a two-edge cut. It is used to show that a three-edge-connected cubic bipartite network with a dual carries a colored dual structure, in which simplicity of $D$ is an axiom.
--
--   **Formalization Note** Duality is the structure `N.Duality D` and simplicity is `D.Simple` (`loopless` and injectivity of $e\mapsto\{\operatorname{tail}_D(e),\operatorname{head}_D(e)\}$ as an element of `Sym2 F`). The vertex type $F$ is not required to be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean#L36-L79

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable {F : Type*} [Fintype F] (D : Network F E)

omit [Fintype F] in
theorem OAI.Barnette.Network.Duality.simple_dual_edge (h : N.Duality D)
    (h3 : N.ThreeEdgeConnected) : D.Simple := by sorry
