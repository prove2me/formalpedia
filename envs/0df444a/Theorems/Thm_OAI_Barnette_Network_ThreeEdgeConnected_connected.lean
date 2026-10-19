-- Prove2me | Theorems.Thm_OAI_Barnette_Network_ThreeEdgeConnected_connected
-- name    : OAI.Barnette.Network.ThreeEdgeConnected.connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:58:29.068005+00:00
-- url     : https://prove2.me/theorems/9f322be2-6bd2-4075-afaf-7706b36f6dca
-- title:
--   Three-edge-connected networks are connected
-- statement:
--   Let $N$ be a finite oriented network with a nonempty vertex set $V$ and edge set $E$. For $A\subseteq V$ let $\delta(A)$ be the set of edges with exactly one endpoint in $A$. Suppose $N$ is *three-edge-connected*: $|\delta(A)|\ge 3$ for every $A\subseteq V$ with $A\neq\emptyset$ and $V\setminus A\neq\emptyset$. Then the underlying simple graph $G_N$, which joins distinct vertices $v,w$ when some edge has endpoints $\{v,w\}$, is connected:
--
--   $$\Bigl(\forall A\subseteq V,\ \emptyset\neq A\neq V\implies|\delta(A)|\ge3\Bigr)\implies G_N\ \text{is connected}.$$
--
--   Three-edge-connectivity is the hypothesis of the main theorem expressed through edge cuts; this lemma recovers ordinary connectivity from it, which is needed for instance to apply duality and quotient arguments. The nonemptiness of $V$ is necessary, since the cut condition is vacuous on a single vertex but connectivity of a graph includes nonemptiness.
--
--   **Formalization Note** The hypothesis is `N.ThreeEdgeConnected`, quantifying over `Finset V` with nonempty set and nonempty complement, and nonemptiness is the instance `[Nonempty V]`; connectivity is Mathlib's `SimpleGraph.Connected` for `N.graph`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean#L242-L256

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

theorem OAI.Barnette.Network.ThreeEdgeConnected.connected [Nonempty V] (h : N.ThreeEdgeConnected) : N.graph.Connected := by sorry
