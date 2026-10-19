-- Prove2me | Theorems.Thm_OAI_Barnette_Network_cap_star_none
-- name    : OAI.Barnette.Network.cap_star_none
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:57:50.445613+00:00
-- url     : https://prove2.me/theorems/7f81e308-9a38-4b6b-97aa-f374dd85d102
-- title:
--   The star of the contracted vertex of a capped network is the cut
-- statement:
--   Let $N$ be an oriented network with vertex set $V$ and finite edge set $E$, every edge $e$ having a tail $\operatorname{tail}(e)$ and a head $\operatorname{head}(e)$, and let $A\subseteq V$ be a finite set. Let $\kappa_A:V\to A\sqcup\{\ast\}$ send $v$ to itself if $v\in A$ and to a new symbol $\ast$ otherwise. The *capped network* $N^A$ has vertex set $A\sqcup\{\ast\}$ and edge set $E_A=\{e\in E:\operatorname{tail}(e)\in A\ \text{or}\ \operatorname{head}(e)\in A\}$, an edge $e\in E_A$ having tail $\kappa_A(\operatorname{tail}(e))$ and head $\kappa_A(\operatorname{head}(e))$. In words, $N^A$ contracts $V\setminus A$ to the single vertex $\ast$ and deletes the edges with both endpoints outside $A$. For a vertex $x$ of a network, $\operatorname{star}(x)$ is the set of edges having $x$ as tail or head. Let $\delta(A)\subseteq E$ be the set of edges of $N$ with exactly one endpoint in $A$.
--
--   Then the edges of $N^A$ at the contracted vertex $\ast$ are exactly the cut edges of $A$:
--
--   $$\operatorname{star}_{N^A}(\ast)=\delta(A)\qquad\text{as subsets of } E.$$
--
--   In particular the degree of $\ast$ in $N^A$ equals the size of the cut, so capping a cubic graph along a three-edge cut produces a vertex of degree three. This is the basic bookkeeping fact for reducing along three-edge cuts.
--
--   **Formalization Note** The capped network is `N.cap A` on `Option A`, with `none` playing the role of $\ast$; the statement compares the image of `(N.cap A).star none` under the subtype inclusion `N.regionEdges A → E` with `N.cut A`. The vertex type $V$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean#L181-L197

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
theorem OAI.Barnette.Network.cap_star_none (A : Finset V) :
    ((N.cap A).star none).image Subtype.val = N.cut A := by sorry
