-- Prove2me | Theorems.Thm_OAI_Barnette_Network_Triangle_corner_iff_incident
-- name    : OAI.Barnette.Network.Triangle.corner_iff_incident
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:09:26.9689+00:00
-- url     : https://prove2.me/theorems/b0e59fdc-1a6d-4ca6-9260-eb1f994e902d
-- title:
--   The corners of a triangle are exactly the vertices incident to its edges
-- statement:
--   A *network* $D$ with vertex set $F$ and edge set $E$ is a pair of maps $\mathrm{tail},\mathrm{head}:E\to F$; an edge $e$ is *incident* to $v$ if $v\in\{\mathrm{tail}(e),\mathrm{head}(e)\}$. A *triangle* of $D$ on a finite set $s\subseteq E$ consists of three distinct vertices $c_0,c_1,c_2$ (its corners) and three distinct edges $e_0,e_1,e_2$ with $\{e_0,e_1,e_2\}=s$, such that the endpoint pair of $e_i$ is $\{c_i,c_{i+1}\}$ for each $i$, indices taken modulo $3$.
--
--   **Theorem.** Let $T$ be a triangle of $D$ on $s$, with corners $c_0,c_1,c_2$. For every vertex $v\in F$,
--
--   $$v\in\{c_0,c_1,c_2\}\iff \exists\,e\in s:\ v\in\{\mathrm{tail}(e),\mathrm{head}(e)\}.$$
--
--   Hence the corner set of a triangle is determined by its edge set alone. This lets one decide whether a vertex is a corner of a triangle by looking only at incidences with the triangle's edges, as is done when triangles are attached to stars of vertices of a dual network.
--
--   **Formalization Note** The corners are `Set.range t.corner` for `t : D.Triangle s`. No finiteness of $E$ or $F$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Bonds.lean#L214-L229

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype E] [Fintype F] in
theorem OAI.Barnette.Network.Triangle.corner_iff_incident {s : Finset E} (t : D.Triangle s) (v : F) :
    v ∈ Set.range t.corner ↔ ∃ e ∈ s, D.Incident e v := by sorry
