-- Prove2me | Theorems.Thm_OAI_Barnette_Network_cap_connectedFibers
-- name    : OAI.Barnette.Network.cap_connectedFibers
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:00:51.467686+00:00
-- url     : https://prove2.me/theorems/1611d7d4-bbaa-4280-82d2-c3494389b07b
-- title:
--   Capping a vertex set with connected complement has connected fibres
-- statement:
--   Let $N$ be an oriented network with vertex set $V$ and edge set $E$ (no finiteness is assumed), every edge $e$ having a tail $\operatorname{tail}(e)$ and a head $\operatorname{head}(e)$, and let $G_N$ be its underlying simple graph, which joins distinct vertices when some edge has exactly these endpoints. Let $A\subseteq V$ be a finite set and $\kappa_A:V\to A\sqcup\{\ast\}$ the capping map, $\kappa_A(v)=v$ for $v\in A$ and $\kappa_A(v)=\ast$ otherwise. Call an edge $e$ *internal* if $\kappa_A(\operatorname{tail}(e))=\kappa_A(\operatorname{head}(e))$, and let $G_{\mathrm{int}}$ be the simple graph on $V$ joining distinct $x,y$ when some internal edge has endpoints $\{x,y\}$.
--
--   Assume that the subgraph of $G_N$ induced on $V\setminus A$ is connected (in particular $V\setminus A\neq\emptyset$). Then $\kappa_A$ has connected fibres: for all $v,w\in V$,
--
--   $$\kappa_A(v)=\kappa_A(w)\implies v\ \text{and}\ w\ \text{are joined by a walk in } G_{\mathrm{int}}.$$
--
--   Connected fibres is the hypothesis under which contracting the fibres of a vertex map preserves the cycle and cut structure of a network, so that duality passes to the contracted network. This lemma verifies it for the capping map, the contraction used to cut a graph along a three-edge cut.
--
--   **Formalization Note** The conclusion is `N.ConnectedFibers (N.capMap A)`, i.e. reachability in the graph of `N.restrict` to the set `N.internal (N.capMap A)` of internal edges; the hypothesis is `(N.graph.induce {v | v ∉ A}).Connected`, and neither $V$ nor $E$ is required to be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean#L270-L292

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

omit [Fintype V] [Fintype E] in
theorem OAI.Barnette.Network.cap_connectedFibers (A : Finset V)
    (hc : (N.graph.induce {v | v ∉ A}).Connected) : N.ConnectedFibers (N.capMap A) := by sorry
