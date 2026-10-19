-- Prove2me | Theorems.Thm_OAI_Barnette_Network_region_balance_rim
-- name    : OAI.Barnette.Network.region_balance_rim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:33:12.044077+00:00
-- url     : https://prove2.me/theorems/53021ccf-05e7-473f-94ef-90388de3de6f
-- title:
--   Color balance of a region equals its black rim count in a two-colored cubic network
-- statement:
--   Let $N$ (vertex set $V$) and $D$ (vertex set $F$) be oriented networks on a common edge set $E$, with $V$ and $E$ finite, given by tail and head maps $t_N,h_N:E\to V$ and $t_D,h_D:E\to F$. For a finite set $U\subseteq F$ of dual vertices, the induced edges are $E_D[U]=\{e\in E: t_D(e)\in U\text{ and }h_D(e)\in U\}$. Deleting them from $N$ leaves the network on $V$ with edge set $E\setminus E_D[U]$. Its regions are the connected components of its underlying simple graph (distinct vertices adjacent when an edge joins them), and the shore $A_q\subseteq V$ of a region $q$ is the set of vertices of $q$. The rim of $q$ counts the ends of induced edges lying on the shore:
--   $$\operatorname{rim}(q)=\sum_{e\in E_D[U]}\big([t_N(e)\in A_q]+[h_N(e)\in A_q]\big),$$
--   where $[\cdot]$ is the Iverson bracket. For a set $B\subseteq V$ of black vertices let $\chi_B(v)=1$ if $v\in B$ and $\chi_B(v)=-1$ otherwise, and define the black rim and the color balance of $q$ by
--   $$\operatorname{rim}_B(q)=\sum_{e\in E_D[U]}\big([t_N(e)\in A_q\cap B]+[h_N(e)\in A_q\cap B]\big),\qquad \beta(q)=\sum_{v\in A_q}\chi_B(v).$$
--
--   **Theorem.** Suppose $N$ is simple (no loops, and distinct edges have distinct unordered endpoint pairs), its underlying graph is $3$-regular, and every edge has exactly one black endpoint ($t_N(e)\in B$ if and only if $h_N(e)\notin B$). Then for every finite $U\subseteq F$ and every region $q$
--
--   $$3\,\beta(q)=2\operatorname{rim}_B(q)-\operatorname{rim}(q).$$
--
--   The identity expresses the excess of black over white vertices in a region through the boundary half-edges of the region alone. It is a localized form of the fact that a properly two-colored cubic graph has equally many vertices of each color: for $U=\varnothing$ there are no induced edges, the regions are the connected components of $N$, and the identity says that every component is balanced. It feeds the counting arguments for contractions of dual networks.
--
--   **Formalization Note** Regions are `N.Regions D U` (connected components of `N.regions D U`), the shore is `N.regionShore D U q`, and $\operatorname{rim}$, $\operatorname{rim}_B$, $\beta$ are `N.rim`, `N.blackRim`, `N.regionBalance` with $\chi_B$ given by `colorSign`. The rims are natural numbers cast to integers. The dual vertex type $F$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Contraction.lean#L222-L255

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
theorem OAI.Barnette.Network.region_balance_rim (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (U : Finset F) (q : N.Regions D U) :
    3 * N.regionBalance D black U q = 2 * (N.blackRim D black U q : ℤ) - N.rim D U q := by sorry
