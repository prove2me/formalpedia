-- Prove2me | Theorems.Thm_OAI_ForestSpace_main_lens_aprox
-- name    : OAI.ForestSpace.main_lens_aprox
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:25:24.446709+00:00
-- url     : https://prove2.me/theorems/9b4747f7-9028-4dd4-9595-0b2cac5631f6
-- title:
--   Approximate separated-midpoint (lens) inequality in the dual space $J(T)^*$
-- statement:
--   Let $T$ be the forest whose vertices are the pairs $(h,s)$ with $h\ge 1$ an integer and $s$ a finite sequence of natural numbers of length at most $h$, ordered by $(h,s)\le(h',s')$ if and only if $h=h'$ and $s$ is an initial segment of $s'$. Thus $T$ is the disjoint union, over $h\ge1$, of the countably branching rooted trees of height $h$. A *segment* of $T$ is a finite chain $S\subseteq T$ that is order-convex ($a,b\in S$ and $a\le c\le b$ imply $c\in S$). Let $J(T)$ be the completion of the space of finitely supported functions $u:T\to\mathbb{R}$ under the disjoint-segment norm
--
--   $$
--   \|u\|=\sup\Big\{\Big(\sum_{i=1}^m\Big(\sum_{v\in S_i}u(v)\Big)^2\Big)^{1/2}\ :\ S_1,\dots,S_m\subseteq T \text{ pairwise disjoint segments}\Big\},
--   $$
--
--   and let $J(T)^*$ be its full continuous dual, with the operator norm.
--
--   Let $R>0$, $\varepsilon>0$ and $0<\eta\le1$. Let $x\in J(T)^*$ and let $(y_j)_{j\in\mathbb{N}}$ be a sequence in $J(T)^*$ such that $\|x+y_j\|\le R$ and $\|x-y_j\|\le R$ for every $j$, and $\|y_i-y_j\|\ge\varepsilon$ for all $i\ne j$. Then
--
--   $$
--   \|x\|^2+\frac{\varepsilon^2}{48}\ \le\ R^2+8(R+1)\,\eta .
--   $$
--
--   Geometrically, all $y_j$ lie in the lens $\{y:\|x+y\|\le R,\ \|x-y\|\le R\}$, and the inequality says, up to the error term $8(R+1)\eta$, that a lens containing an infinite $\varepsilon$-separated sequence satisfies $R^2-\|x\|^2\ge\varepsilon^2/48$. Since $\eta\in(0,1]$ is arbitrary, the error term can be made as small as desired, and letting $\eta\to0$ gives the exact lens inequality $\varepsilon^2/48\le R^2-\|x\|^2$.
--
--   **Formalization Note** $T$ is the type `Vertex` (a height `h ≥ 1` and a `Word` of length at most `h`, ordered by equal height and list prefix), `J Vertex` is the uniform completion of `TestVector Vertex` (finitely supported functions with the segment norm `rho`), and $J(T)^*$ is `FullDual Vertex = StrongDual ℝ (J Vertex)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Lens.lean#L67-L133

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
import Definitions.Def_OAI_Analysis_ForestSpace_Trees
import Definitions.Def_OAI_Analysis_ForestSpace_Reflexivity
import Definitions.Def_OAI_Analysis_ForestSpace_Components
import Definitions.Def_OAI_Analysis_ForestSpace_FullDual

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.ForestSpace.main_lens_aprox (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (x : FullDual Vertex) (y : ℕ → FullDual Vertex)
    (hp : ∀ j, ‖x+y j‖ ≤ R) (hm : ∀ j, ‖x-y j‖ ≤ R)
    (hs : ∀ i j, i ≠ j → ε ≤ ‖y i-y j‖)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ‖x‖^2+ε^2/48 ≤ R^2+8*(R+1)*η := by sorry
