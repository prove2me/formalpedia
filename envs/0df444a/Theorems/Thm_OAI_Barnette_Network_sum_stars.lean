-- Prove2me | Theorems.Thm_OAI_Barnette_Network_sum_stars
-- name    : OAI.Barnette.Network.sum_stars
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:13:07.391191+00:00
-- url     : https://prove2.me/theorems/ac3964bf-e81d-4c58-950e-422448aa1bb6
-- title:
--   Double counting vertex–edge incidences over a vertex set
-- statement:
--   Let $N$ be a network with vertex set $V$ and finite edge set $E$: each edge $e$ has a tail $t(e)\in V$ and a head $h(e)\in V$. The network is *simple* if it has no loops ($t(e)\neq h(e)$ for every $e$) and no two edges have the same unordered pair of endpoints. For $v\in V$ let $\operatorname{st}(v)=\{e\in E: t(e)=v\ \text{or}\ h(e)=v\}$ be the star of $v$, and for a statement $P$ write $[P]$ for $1$ if $P$ holds and $0$ otherwise.
--
--   If $N$ is simple, then for every finite set $A\subseteq V$
--
--   $$
--   \sum_{v\in A}|\operatorname{st}(v)|=\sum_{e\in E}\bigl([t(e)\in A]+[h(e)\in A]\bigr).
--   $$
--
--   This is the handshake double count of incidences between edges and vertices of $A$: every edge is counted once for each of its endpoints that lies in $A$. It is the common starting point for the edge-counting identities for regions of cubic networks, for example $3|A|+|\delta(A)|=2|E_A|$.
--
--   **Formalization Note** Only the looplessness part of simplicity is used. Both sides are natural numbers, and the vertex type need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/DiskRegions.lean#L269-L288

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

omit [Fintype V] in
theorem OAI.Barnette.Network.sum_stars (hN : N.Simple) (A : Finset V) :
    ∑ v ∈ A, (N.star v).card =
      ∑ e, ((if N.tail e ∈ A then 1 else 0) + (if N.head e ∈ A then 1 else 0)) := by sorry
