-- Prove2me | Theorems.Thm_OAI_Barnette_Network_card_star
-- name    : OAI.Barnette.Network.card_star
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:06:51.036481+00:00
-- url     : https://prove2.me/theorems/03cc3ffd-744d-4ccb-bb9e-806b54b88950
-- title:
--   In a simple network the number of edges at a vertex equals its degree in the underlying graph
-- statement:
--   A *network* $N$ with finite vertex set $V$ and finite edge set $E$ is a pair of maps $\mathrm{tail},\mathrm{head}:E\to V$. Its underlying graph $G(N)$ is the simple graph on $V$ in which distinct $v,w$ are adjacent iff some edge $e$ has endpoint pair $\{\mathrm{tail}(e),\mathrm{head}(e)\}=\{v,w\}$. The network is *simple* if $\mathrm{tail}(e)\ne\mathrm{head}(e)$ for every $e$ and distinct edges have distinct endpoint pairs. The *star* of a vertex $v$ is the set of edges incident to $v$,
--
--   $$\operatorname{star}_N(v)=\{e\in E:\ v\in\{\mathrm{tail}(e),\mathrm{head}(e)\}\}.$$
--
--   **Theorem.** If $N$ is simple, then for every vertex $v$
--
--   $$|\operatorname{star}_N(v)|=\deg_{G(N)}(v).$$
--
--   For simple networks the star of a vertex is thus a faithful edge-level copy of its neighbourhood, so degree hypotheses on $G(N)$, such as cubicity, can be used directly as statements about the edges at each vertex.
--
--   **Formalization Note** The star is `N.star v`, a `Finset E`, and the degree is Mathlib's `N.graph.degree v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/FlowCircuits.lean#L160-L182

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

theorem OAI.Barnette.Network.card_star (h : N.Simple) (v : V) : (N.star v).card = N.graph.degree v := by sorry
