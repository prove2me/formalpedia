-- Prove2me | Theorems.Thm_OAI_Barnette_Network_rim_cut_count
-- name    : OAI.Barnette.Network.rim_cut_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:33:45.638972+00:00
-- url     : https://prove2.me/theorems/2e3d321d-8178-449c-badc-f9919696ba54
-- title:
--   The rim of a region counts its cut edges once and its internal induced edges twice
-- statement:
--   Let $N$ (vertex set $V$) and $D$ (vertex set $F$) be oriented networks on a common edge set $E$, with $V$ and $E$ finite, given by tail and head maps $t_N,h_N:E\to V$ and $t_D,h_D:E\to F$. For a finite set $U\subseteq F$ of dual vertices, the induced edges are $E_D[U]=\{e\in E: t_D(e)\in U\text{ and }h_D(e)\in U\}$. Deleting them from $N$ leaves the network on $V$ with edge set $E\setminus E_D[U]$. Its regions are the connected components of its underlying simple graph (distinct vertices adjacent when an edge joins them), and the shore $A_q\subseteq V$ of a region $q$ is the set of vertices of $q$. The rim of $q$ counts the ends of induced edges lying on the shore:
--   $$\operatorname{rim}(q)=\sum_{e\in E_D[U]}\big([t_N(e)\in A_q]+[h_N(e)\in A_q]\big),$$
--   where $[\cdot]$ is the Iverson bracket. The cut of a set $A\subseteq V$ is $\partial A=\{e\in E:\ \text{exactly one of } t_N(e),h_N(e) \text{ lies in } A\}$.
--
--   **Theorem.** For every finite $U\subseteq F$ and every region $q$
--
--   $$\operatorname{rim}(q)=|\partial A_q|+2\,\big|\{e\in E_D[U]:\ t_N(e)\in A_q\ \text{and}\ h_N(e)\in A_q\}\big|.$$
--
--   No hypothesis on $N$ or $D$ is needed. In particular $|\partial A_q|\le\operatorname{rim}(q)$, with equality exactly when no induced edge has both ends on the shore. These are the facts used to identify small edge cuts around regions when dual networks are contracted.
--
--   **Formalization Note** The shore is `N.regionShore D U q`, the cut is `N.cut`, the induced edges are `D.inducedEdges U`, and the rim is the natural number `N.rim D U q`. The dual vertex type $F$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Contraction.lean#L304-L319

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
theorem OAI.Barnette.Network.rim_cut_count (U : Finset F) (q : N.Regions D U) :
    N.rim D U q = (N.cut (N.regionShore D U q)).card +
      2 * ((D.inducedEdges U).filter fun e =>
        N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q).card := by sorry
