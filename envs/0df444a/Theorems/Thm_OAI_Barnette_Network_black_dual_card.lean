-- Prove2me | Theorems.Thm_OAI_Barnette_Network_black_dual_card
-- name    : OAI.Barnette.Network.black_dual_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:42:14.317769+00:00
-- url     : https://prove2.me/theorems/8e0a29d4-4d5a-427a-ba7c-f8029c4e3fdf
-- title:
--   A cubic properly two-colored network with an exact dual has $|B|+2$ dual vertices
-- statement:
--   Let $N$ (vertex set $V$) and $D$ (vertex set $F$) be oriented networks on a common edge set $E$, all finite, with tail and head maps $t_N,h_N:E\to V$ and $t_D,h_D:E\to F$. The gradient is $(\nabla_N g)(e)=g(h_N(e))-g(t_N(e))$ and the boundary is $(\partial_N x)(u)=\sum_{e:\,h_N(e)=u}x(e)-\sum_{e:\,t_N(e)=u}x(e)$, and $\nabla_D,\partial_D$ are defined in the same way. The networks are in duality if their underlying simple graphs are connected and
--   $$\ker\partial_N=\operatorname{im}\nabla_D,\qquad \ker\partial_D=\operatorname{im}\nabla_N$$
--   (cycle spaces equal the cut spaces of the other network).
--
--   **Theorem.** Suppose $N$ and $D$ are in duality, $N$ is simple (no loops, and distinct edges have distinct unordered endpoint pairs), the underlying graph of $N$ is $3$-regular, and $B\subseteq V$ is a set of black vertices such that every edge has exactly one black endpoint. Then
--
--   $$|F|=|B|+2 .$$
--
--   If $N$ is a cubic bipartite plane graph and $D$ its face network, this is the Euler-formula count of faces, $|F|=\tfrac12|V|+2$, written in terms of one color class.
--
--   **Formalization Note** Duality is the structure `N.Duality D`, simplicity is `N.Simple`, cubicity is `N.graph.IsRegularOfDegree 3`, and the black class is `Finset.univ.filter black`. The cardinality $|F|$ is `Fintype.card F`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/MinorDuality.lean#L179-L192

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

theorem OAI.Barnette.Network.black_dual_card (h : N.Duality D) (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    Fintype.card F = (Finset.univ.filter black).card + 2 := by sorry
