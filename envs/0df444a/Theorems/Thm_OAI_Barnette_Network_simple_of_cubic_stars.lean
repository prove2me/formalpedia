-- Prove2me | Theorems.Thm_OAI_Barnette_Network_simple_of_cubic_stars
-- name    : OAI.Barnette.Network.simple_of_cubic_stars
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:03:02.32701+00:00
-- url     : https://prove2.me/theorems/1c3162ab-d638-4fc8-aa30-b92e8dd73d88
-- title:
--   A loopless 3-edge-connected network with three edges at every vertex and at least three vertices is simple
-- statement:
--   A *network* $N$ consists of finite sets $V$ (vertices) and $E$ (edges) together with maps $t,h:E\to V$ giving the tail and the head of each edge; parallel edges and loops are allowed a priori. For $v\in V$ let $\operatorname{star}(v)=\{e\in E: t(e)=v\text{ or }h(e)=v\}$ be the set of edges incident with $v$, and for $A\subseteq V$ let
--   $$\delta(A)=\{e\in E:\ \text{exactly one of } t(e),h(e) \text{ lies in } A\}$$
--   be the edge cut of $A$. The network is *3-edge-connected* if $|\delta(A)|\ge 3$ for every $A\subseteq V$ with $A\neq\varnothing$ and $A\neq V$. It is *simple* if it has no loops and distinct edges have distinct unordered endpoint pairs.
--
--   **Theorem.** Suppose that $t(e)\neq h(e)$ for every edge $e$, that $|\operatorname{star}(v)|=3$ for every vertex $v$, that $N$ is 3-edge-connected, and that $|V|\ge 3$. Then $N$ is simple; that is, besides being loopless it satisfies
--
--   $$
--   e\neq f\ \Longrightarrow\ \{t(e),h(e)\}\neq\{t(f),h(f)\}\qquad\text{for all } e,f\in E .
--   $$
--
--   The point of the lemma is that simplicity of a network can be read off from purely local data (every star has three edges, no loops) together with global edge connectivity. It is applied to the network obtained by contracting one side of a 3-edge cut of a simple cubic 3-edge-connected network, to show that this capped network is again simple and hence again cubic.
--
--   **Formalization Note** The network is `Network V E` with fields `tail` and `head`; `N.Simple` consists of looplessness and injectivity of `e ↦ s(tail e, head e)` into unordered pairs `Sym2 V`; `ThreeEdgeConnected` quantifies over finite vertex sets `A` with `A.Nonempty` and `Aᶜ.Nonempty`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean#L300-L350

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

theorem OAI.Barnette.Network.simple_of_cubic_stars (hl : ∀ e, N.tail e ≠ N.head e)
    (hc : ∀ v, (N.star v).card = 3) (h3 : N.ThreeEdgeConnected)
    (hV : 3 ≤ Fintype.card V) : N.Simple := by sorry
