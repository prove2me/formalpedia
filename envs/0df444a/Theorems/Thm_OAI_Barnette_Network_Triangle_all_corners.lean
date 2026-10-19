-- Prove2me | Theorems.Thm_OAI_Barnette_Network_Triangle_all_corners
-- name    : OAI.Barnette.Network.Triangle.all_corners
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:39:20.095715+00:00
-- url     : https://prove2.me/theorems/8a8a231d-5e91-4eae-bad7-3608f258f8ac
-- title:
--   A triangle lies among the induced edges of $U$ iff all its corners lie in $U$
-- statement:
--   Let $D$ be an oriented network with vertex set $F$, finite edge set $E$, and tail and head maps $t_D,h_D:E\to F$. For a finite set $U\subseteq F$ the induced edges are $E_D[U]=\{e\in E: t_D(e)\in U\text{ and }h_D(e)\in U\}$. A triangle of $D$ on an edge set $S\subseteq E$ consists of three distinct corners $c_0,c_1,c_2\in F$ and three distinct edges $e_0,e_1,e_2$ with $\{e_0,e_1,e_2\}=S$, such that for each $i\in\mathbb{Z}/3$ the edge $e_i$ joins $c_i$ and $c_{i+1}$ in $D$ (in either direction).
--
--   **Theorem.** For every triangle of $D$ on an edge set $S$ and every finite $U\subseteq F$,
--
--   $$S\subseteq E_D[U]\iff c_0,c_1,c_2\in U .$$
--
--   In the dual network of a cubic plane graph the triangle on the star of a vertex is the face triangle of that vertex. The statement says that this face triangle survives in the subnetwork induced by $U$ exactly when all three faces around the vertex are selected.
--
--   **Formalization Note** The triangle is `t : D.Triangle s` with corners `t.corner` and edges `t.edge`, and $E_D[U]$ is `D.inducedEdges U`. Neither the primal nor the dual vertex type needs to be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/MinorDuality.lean#L140-L156

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

omit [Fintype V] [Fintype F] in
theorem OAI.Barnette.Network.Triangle.all_corners {s : Finset E} (t : D.Triangle s) (U : Finset F) :
    s ⊆ D.inducedEdges U ↔ ∀ i, t.corner i ∈ U := by sorry
