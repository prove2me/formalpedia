-- Prove2me | Theorems.Thm_OAI_Barnette_Network_rim_three_cut
-- name    : OAI.Barnette.Network.rim_three_cut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:35:31.119865+00:00
-- url     : https://prove2.me/theorems/f606bb79-f982-47e4-a00e-cc03509ab458
-- title:
--   In a three-edge-connected network a region of rim three has a three-edge cut
-- statement:
--   Let $N$ (vertex set $V$) and $D$ (vertex set $F$) be oriented networks on a common edge set $E$, with $V$ and $E$ finite, given by tail and head maps $t_N,h_N:E\to V$ and $t_D,h_D:E\to F$. For a finite set $U\subseteq F$ of dual vertices, the induced edges are $E_D[U]=\{e\in E: t_D(e)\in U\text{ and }h_D(e)\in U\}$. Deleting them from $N$ leaves the network on $V$ with edge set $E\setminus E_D[U]$. Its regions are the connected components of its underlying simple graph (distinct vertices adjacent when an edge joins them), and the shore $A_q\subseteq V$ of a region $q$ is the set of vertices of $q$. The rim of $q$ counts the ends of induced edges lying on the shore:
--   $$\operatorname{rim}(q)=\sum_{e\in E_D[U]}\big([t_N(e)\in A_q]+[h_N(e)\in A_q]\big),$$
--   where $[\cdot]$ is the Iverson bracket. The cut of $A\subseteq V$ is $\partial A=\{e:\ \text{exactly one of } t_N(e),h_N(e)\text{ lies in }A\}$, and $N$ is three-edge-connected if $|\partial A|\ge3$ for every $A\subseteq V$ with $A\ne\varnothing$ and $V\setminus A\ne\varnothing$.
--
--   **Theorem.** Suppose $N$ is three-edge-connected. Let $U\subseteq F$ be finite with $|E_D[U]|\ge3$, and let $q$ be a region with $\operatorname{rim}(q)=3$. Then
--
--   $$|\partial A_q|=3 .$$
--
--   So a region touching the induced edges in only three edge-ends is cut off from the rest of $N$ by exactly three edges, and no induced edge lies inside its shore. This is the starting point for analysing three-edge cuts created when a dual network is contracted.
--
--   **Formalization Note** Three-edge-connectivity is `N.ThreeEdgeConnected`. The hypothesis $|E_D[U]|\ge3$ is part of the statement but is not needed by the proof (it is named `_hm`). The dual vertex type $F$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Contraction.lean#L345-L359

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
theorem OAI.Barnette.Network.rim_three_cut (hN : N.ThreeEdgeConnected) (U : Finset F)
    (_hm : 3 ≤ (D.inducedEdges U).card) (q : N.Regions D U) (hq : N.rim D U q = 3) :
    (N.cut (N.regionShore D U q)).card = 3 := by sorry
