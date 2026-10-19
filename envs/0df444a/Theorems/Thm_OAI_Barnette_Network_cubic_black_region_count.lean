-- Prove2me | Theorems.Thm_OAI_Barnette_Network_cubic_black_region_count
-- name    : OAI.Barnette.Network.cubic_black_region_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:17:45.094999+00:00
-- url     : https://prove2.me/theorems/a533b4d0-ad7f-46a8-872f-623df39013f5
-- title:
--   Counting black vertices of a region in a properly two-coloured cubic network
-- statement:
--   Let $N$ be a network with finite vertex set $V$ and finite edge set $E$, each edge $e$ having a tail $t(e)$ and a head $h(e)$ in $V$. Assume $N$ is *simple* (no loops, and no two edges with the same unordered pair of endpoints) and that its underlying graph $G(N)$ (distinct vertices adjacent when some edge joins them) is $3$-regular. Let $B\subseteq V$ be a set of *black* vertices such that every edge has exactly one black endpoint, i.e. $t(e)\in B$ if and only if $h(e)\notin B$; write $b(e)$ for the black endpoint of $e$. For $A\subseteq V$ let
--
--   * $\delta(A)$ be the set of edges with exactly one endpoint in $A$;
--   * $E_A$ be the set of edges with at least one endpoint in $A$;
--   * $\delta_B(A)=\{e\in\delta(A): b(e)\in A\}$ be the cut edges whose black endpoint lies in $A$.
--
--   Then for every $A\subseteq V$
--
--   $$
--   3\,|A\cap B|+|\delta(A)|=|E_A|+|\delta_B(A)|.
--   $$
--
--   This is the black analogue of the count $3|A|+|\delta(A)|=2|E_A|$: every edge of $E_A$ has one black endpoint, which may or may not lie in $A$. Together with that count and the Euler formula for dual regions, it pins down the imbalance between the black and the white endpoints of a cut bounding a disk in a cubic bipartite plane graph.
--
--   **Formalization Note** The colouring is a predicate `black : V → Prop` with hypothesis `∀ e, black (N.tail e) ↔ ¬black (N.head e)`. The black endpoint $b(e)$ is `N.blackEndpoint black e` (the tail if it is black, otherwise the head), $\delta_B(A)$ is `N.blackCut black A`, and $|A\cap B|$ is `(A.filter black).card`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/StateDisk.lean#L238-L258

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
theorem OAI.Barnette.Network.cubic_black_region_count (sN : N.Simple) (hdeg : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) :
    3 * (A.filter black).card + (N.cut A).card =
      (N.regionEdges A).card + (N.blackCut black A).card := by sorry
