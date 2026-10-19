-- Prove2me | Theorems.Thm_OAI_Barnette_Network_triangle_of_flow
-- name    : OAI.Barnette.Network.triangle_of_flow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:05:43.888876+00:00
-- url     : https://prove2.me/theorems/a031c64a-4d73-48ed-8ce7-96933dc33b7d
-- title:
--   A circulation supported on exactly three edges of a simple network lives on a triangle
-- statement:
--   A *network* $N$ with vertex set $V$ and finite edge set $E$ is a pair of maps $\mathrm{tail},\mathrm{head}:E\to V$ (loops and parallel edges are allowed a priori). An edge $e$ is *incident* to a vertex $v$ if $v\in\{\mathrm{tail}(e),\mathrm{head}(e)\}$. The network is *simple* if it has no loops, $\mathrm{tail}(e)\ne\mathrm{head}(e)$ for all $e$, and distinct edges have distinct endpoint pairs $\{\mathrm{tail}(e),\mathrm{head}(e)\}$. The *boundary* of an edge function $x:E\to\mathbb{R}$ is the vertex function giving the net inflow at each vertex,
--
--   $$(\partial_N x)(v)=\sum_{e:\ \mathrm{head}(e)=v}x_e\;-\sum_{e:\ \mathrm{tail}(e)=v}x_e ,$$
--
--   and $x$ is a *circulation* if $\partial_N x=0$. Its *support* is $\operatorname{supp}x=\{e\in E:\ x_e\ne0\}$.
--
--   A *triangle* on a set $s\subseteq E$ consists of three distinct vertices $c_0,c_1,c_2$ (its corners) and three distinct edges $e_0,e_1,e_2$ with $\{e_0,e_1,e_2\}=s$, such that the endpoint pair of $e_i$ is $\{c_i,c_{i+1}\}$ for each $i$, indices taken modulo $3$.
--
--   **Theorem.** Let $N$ be a simple network and $x$ a circulation of $N$ whose support has exactly three edges. Then $\operatorname{supp}x$ carries a triangle: there are distinct vertices $c_0,c_1,c_2$ and an enumeration of the support by distinct edges with
--
--   $$\operatorname{supp}x=\{e_0,e_1,e_2\},\qquad \{\mathrm{tail}(e_i),\mathrm{head}(e_i)\}=\{c_i,c_{i+1}\}\quad(i\in\mathbb{Z}/3\mathbb{Z}).$$
--
--   The result converts a purely algebraic condition, a circulation with a three-edge support, into the combinatorial structure of a triangle with its corners and cyclically ordered sides, which is how triangular faces are recognised from circulations.
--
--   **Formalization Note** The vertex type $V$ need not be finite. The conclusion is `Nonempty (N.Triangle (N.flowSupport x))`, where a `Triangle s` stores injective maps `corner : Fin 3 → V` and `edge : Fin 3 → E` with `Finset.univ.image edge = s` and unordered endpoint pairs `s(N.tail (edge i), N.head (edge i)) = s(corner i, corner (i+1))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/CutSpaces.lean#L230-L310

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
theorem OAI.Barnette.Network.triangle_of_flow (hN : N.Simple) (x : E → ℝ) (hx : N.boundary x = 0)
    (hs : (N.flowSupport x).card = 3) : Nonempty (N.Triangle (N.flowSupport x)) := by sorry
