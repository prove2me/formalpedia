-- Prove2me | Theorems.Thm_OAI_Barnette_Network_nontrivial_threeCut
-- name    : OAI.Barnette.Network.nontrivial_threeCut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:05:01.033154+00:00
-- url     : https://prove2.me/theorems/78575090-1ccc-4310-a2d0-e9b4d10dc9fa
-- title:
--   A network with a nontrivial 3-edge cut has a 3-edge cut with at least two vertices on each side
-- statement:
--   A *network* $N$ consists of finite sets $V$ (vertices) and $E$ (edges) together with maps $t,h:E\to V$ giving the tail and the head of each edge; parallel edges and loops are allowed a priori. For $A\subseteq V$ let $\delta(A)$ be the set of edges with exactly one endpoint in $A$. Say that $N$ has *only trivial 3-edge cuts* if every $A\subseteq V$ with $|\delta(A)|=3$ satisfies $|A|=1$ or $|V\setminus A|=1$.
--
--   **Theorem.** If $N$ does not have only trivial 3-edge cuts, then there is a set $A\subseteq V$ with
--
--   $$
--   |\delta(A)|=3,\qquad |A|\ge 2,\qquad |V\setminus A|\ge 2 .
--   $$
--
--   No further hypothesis on $N$ is needed. In a cubic graph the three edges at a single vertex always form a trivial 3-edge cut; the lemma converts the mere failure of triviality into a cut with at least two vertices on each side, which is exactly the size condition required for capping either side of the cut and obtaining smaller cubic graphs.
--
--   **Formalization Note** Vertex sets are `Finset V`, the complement $V\setminus A$ is `Aᶜ`, and the hypothesis is `¬ N.TrivialThreeCuts`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/CappedDuality.lean#L167-L179

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
universe uF
variable {V E : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

theorem OAI.Barnette.Network.nontrivial_threeCut (h : ¬N.TrivialThreeCuts) :
    ∃ A : Finset V, (N.cut A).card = 3 ∧ 2 ≤ A.card ∧ 2 ≤ Aᶜ.card := by sorry
