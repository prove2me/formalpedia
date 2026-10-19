-- Prove2me | Theorems.Thm_OAI_Barnette_Network_flow_no_leaf
-- name    : OAI.Barnette.Network.flow_no_leaf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:05:16.710494+00:00
-- url     : https://prove2.me/theorems/172d1e52-e839-4ae3-a1ea-f69061de8d28
-- title:
--   The support of a circulation in a simple network has no leaves
-- statement:
--   A *network* $N$ with vertex set $V$ and finite edge set $E$ is a pair of maps $\mathrm{tail},\mathrm{head}:E\to V$ (loops and parallel edges are allowed a priori). An edge $e$ is *incident* to a vertex $v$ if $v\in\{\mathrm{tail}(e),\mathrm{head}(e)\}$. The network is *simple* if it has no loops, $\mathrm{tail}(e)\ne\mathrm{head}(e)$ for all $e$, and distinct edges have distinct endpoint pairs $\{\mathrm{tail}(e),\mathrm{head}(e)\}$. The *boundary* of an edge function $x:E\to\mathbb{R}$ is the vertex function giving the net inflow at each vertex,
--
--   $$(\partial_N x)(v)=\sum_{e:\ \mathrm{head}(e)=v}x_e\;-\sum_{e:\ \mathrm{tail}(e)=v}x_e ,$$
--
--   and $x$ is a *circulation* if $\partial_N x=0$. Its *support* is $\operatorname{supp}x=\{e\in E:\ x_e\ne0\}$.
--
--   **Theorem.** Let $N$ be a simple network and $x$ a circulation of $N$. If $e\in E$ satisfies $x_e\ne0$ and $e$ is incident to a vertex $v$, then some other edge carrying nonzero flow is incident to $v$:
--
--   $$x_e\ne0,\ \ v\in\{\mathrm{tail}(e),\mathrm{head}(e)\}\ \Longrightarrow\ \exists\,f\ne e:\ \ x_f\ne0,\ \ v\in\{\mathrm{tail}(f),\mathrm{head}(f)\}.$$
--
--   Equivalently, in the subgraph formed by the support of a circulation no vertex has degree one. This local fact is the basic tool for identifying small or cycle-shaped circulation supports, such as triangles and supports contained in a cycle.
--
--   **Formalization Note** The vertex type $V$ need not be finite. The boundary is `N.boundary`, a linear map `(E → ℝ) →ₗ[ℝ] (V → ℝ)`, and incidence is `N.Incident e v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/CutSpaces.lean#L196-L220

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
theorem OAI.Barnette.Network.flow_no_leaf (hN : N.Simple) (x : E → ℝ) (hx : N.boundary x = 0)
    {e : E} {v : V} (he : x e ≠ 0) (hev : N.Incident e v) :
    ∃ f, f ≠ e ∧ x f ≠ 0 ∧ N.Incident f v := by sorry
