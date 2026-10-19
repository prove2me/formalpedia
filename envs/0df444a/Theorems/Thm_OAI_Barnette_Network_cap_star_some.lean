-- Prove2me | Theorems.Thm_OAI_Barnette_Network_cap_star_some
-- name    : OAI.Barnette.Network.cap_star_some
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:55:36.212534+00:00
-- url     : https://prove2.me/theorems/4ffd1706-f6ab-48ac-9ef1-2132c5f82a87
-- title:
--   Stars of uncontracted vertices in a capped network
-- statement:
--   Let $N$ be an oriented network with vertex set $V$ and finite edge set $E$, every edge $e$ having a tail $\operatorname{tail}(e)$ and a head $\operatorname{head}(e)$, and let $A\subseteq V$ be a finite set. Let $\kappa_A:V\to A\sqcup\{\ast\}$ send $v$ to itself if $v\in A$ and to a new symbol $\ast$ otherwise. The *capped network* $N^A$ has vertex set $A\sqcup\{\ast\}$ and edge set $E_A=\{e\in E:\operatorname{tail}(e)\in A\ \text{or}\ \operatorname{head}(e)\in A\}$, an edge $e\in E_A$ having tail $\kappa_A(\operatorname{tail}(e))$ and head $\kappa_A(\operatorname{head}(e))$. In words, $N^A$ contracts $V\setminus A$ to the single vertex $\ast$ and deletes the edges with both endpoints outside $A$. For a vertex $x$ of a network, $\operatorname{star}(x)$ is the set of edges having $x$ as tail or head.
--
--   Then for every $v\in A$, the edges of $N^A$ at $v$ are exactly the edges of $N$ at $v$:
--
--   $$\operatorname{star}_{N^A}(v)=\operatorname{star}_N(v)\qquad\text{as subsets of } E.$$
--
--   Capping is the basic operation for splitting a graph along a three-edge cut into two smaller graphs. This lemma, together with its companion for the contracted vertex $\ast$, shows that the capped graph of a cubic graph along a three-edge cut is again cubic and is used when gluing structures back across the cut.
--
--   **Formalization Note** The capped network is `N.cap A`, a network on `Option A` (with `none` playing the role of $\ast$) whose edge type is the subtype of `N.regionEdges A`; the equality compares the image of `(N.cap A).star (some v)` under the subtype inclusion with `N.star v`. The vertex type $V$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean#L165-L179

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

omit [Fintype V] in
theorem OAI.Barnette.Network.cap_star_some (A : Finset V) (v : A) :
    ((N.cap A).star (some v)).image Subtype.val = N.star v.val := by sorry
