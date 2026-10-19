-- Prove2me | Theorems.Thm_OAI_Barnette_Network_cubic_region_count
-- name    : OAI.Barnette.Network.cubic_region_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:13:50.761865+00:00
-- url     : https://prove2.me/theorems/83948320-fc6c-45b5-b105-2cd8bc845807
-- title:
--   Edge count $3|A|+|\delta(A)|=2|E_A|$ in a simple cubic network
-- statement:
--   Let $N$ be a network with finite vertex set $V$ and finite edge set $E$, each edge $e$ having a tail $t(e)$ and a head $h(e)$ in $V$. Assume $N$ is *simple* (no loops, and no two edges with the same unordered pair of endpoints) and that its underlying graph $G(N)$ (distinct vertices are adjacent when some edge joins them) is $3$-regular. For $A\subseteq V$ let
--
--   * $\delta(A)$ be the cut of $A$: the set of edges with exactly one endpoint in $A$;
--   * $E_A$ be the set of edges with at least one endpoint in $A$.
--
--   Then for every $A\subseteq V$
--
--   $$
--   3|A|+|\delta(A)|=2|E_A|.
--   $$
--
--   Each edge with both endpoints in $A$ is counted twice by the degrees on the left, while a cut edge is counted once by the degrees and once more by $|\delta(A)|$. This identity is one of the linear relations which, combined with the Euler formula for dual regions, determine the size of cuts bounding disks in cubic plane graphs; for $A=V$ it reduces to $3|V|=2|E|$.
--
--   **Formalization Note** Regularity is `N.graph.IsRegularOfDegree 3`; $\delta(A)$ is `N.cut A` and $E_A$ is `N.regionEdges A`. All quantities are natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/DiskRegions.lean#L290-L303

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

theorem OAI.Barnette.Network.cubic_region_count (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3) (A : Finset V) :
    3 * A.card + (N.cut A).card = 2 * (N.regionEdges A).card := by sorry
