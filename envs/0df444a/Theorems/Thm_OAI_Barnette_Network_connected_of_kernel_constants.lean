-- Prove2me | Theorems.Thm_OAI_Barnette_Network_connected_of_kernel_constants
-- name    : OAI.Barnette.Network.connected_of_kernel_constants
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:32:20.043979+00:00
-- url     : https://prove2.me/theorems/15ccd860-6268-49c2-abe6-6e64c84d16e4
-- title:
--   A network whose gradient kernel consists of constants is connected
-- statement:
--   Let $N$ be an oriented network with a nonempty vertex set $V$ and an edge set $E$, given by tail and head maps $t,h:E\to V$. Its gradient sends $g:V\to\mathbb{R}$ to the edge function $(\nabla_N g)(e)=g(h(e))-g(t(e))$. Its underlying simple graph $G_N$ joins two distinct vertices $v,w$ whenever some edge $e$ has endpoints $\{t(e),h(e)\}=\{v,w\}$; loops are ignored.
--
--   **Theorem.** If the only real functions with vanishing gradient are constants, i.e.
--
--   $$\forall g:V\to\mathbb{R}:\qquad \nabla_N g=0\ \Longrightarrow\ g(v)=g(w)\ \text{ for all } v,w\in V,$$
--
--   then $G_N$ is connected.
--
--   This is one direction of the standard description of the kernel of the gradient, which is spanned by the indicator functions of the connected components. It allows connectivity, part of the duality hypotheses on networks, to be verified by linear algebra: it suffices to show that $\nabla_N$ has a one-dimensional kernel.
--
--   **Formalization Note** The graph is `N.graph` and connectivity is Mathlib's `SimpleGraph.Connected`, which includes nonemptiness; hence the assumption `Nonempty V`. Neither $V$ nor $E$ needs to be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Forest.lean#L248-L264

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
theorem OAI.Barnette.Network.connected_of_kernel_constants [Nonempty V]
    (hc : ∀ f : V → ℝ, N.gradient f = 0 → ∀ v w, f v = f w) : N.graph.Connected := by sorry
