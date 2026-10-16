-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_trace_zero_of_determinant_one
-- name    : OAI.BoxTransport.Routing.trace_zero_of_determinant_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:14:39.71299+00:00
-- url     : https://prove2.me/theorems/b5dc0ab2-6c1b-4bcb-a082-59f65cdc022c
-- title:
--   Logarithmic velocities of a unit-determinant diagonal scaling sum to zero
-- statement:
--   Let $d:\mathbb{R}\to\mathbb{R}^3$ be a curve with coordinates $d_1,d_2,d_3$, let $l\in\mathbb{R}^3$ and $t\in\mathbb{R}$. Assume that for each $j\in\{1,2,3\}$ the coordinate $s\mapsto d_j(s)$ is differentiable at $t$ with
--
--   $$d_j'(t)=l_j\,d_j(t),$$
--
--   and that $d_1(s)\,d_2(s)\,d_3(s)=1$ for all $s\in\mathbb{R}$. Then
--
--   $$l_1+l_2+l_3=0 .$$
--
--   In matrix language: if $s\mapsto\operatorname{diag}(d(s))$ is a curve of diagonal matrices of determinant one, then its logarithmic velocity $\operatorname{diag}(l)$ at any time is traceless. In the box-routing construction every box is stretched by such a volume-preserving diagonal scaling, and the lemma shows that the induced linear velocity field $x\mapsto(l_1x_1,l_2x_2,l_3x_3)$ is divergence free, as an incompressible flow requires.
--
--   **Formalization Note** Differentiability with the prescribed derivative is `HasDerivAt (fun s => d s j) (l j * d t j) t`, and the determinant condition is a product over `Fin 3`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Flow.lean#L545-L561

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow

open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.trace_zero_of_determinant_one {d : ℝ → Space} {l : Space} {t : ℝ}
    (hd : ∀ j, HasDerivAt (fun s => d s j) (l j * d t j) t)
    (hdet : ∀ s, ∏ j : Fin 3, d s j = 1) : ∑ j : Fin 3, l j = 0 := by sorry
