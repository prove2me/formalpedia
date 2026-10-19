-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_pairNormingFunctional_separates
-- name    : OAI.ReflexiveFixedPoints.pairNormingFunctional_separates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:03:55.141981+00:00
-- url     : https://prove2.me/theorems/f2c724c7-ca37-4f59-829e-6e7bcbe70cc7
-- title:
--   Norming functionals of dense pairs separate points
-- statement:
--   Let $(z_j)$ be dense in $K\subseteq X$, and for each pair $(i,j)$ let $\varphi_{ij}$ be a functional with $\|\varphi_{ij}\|\le1$ and $\varphi_{ij}(z_i-z_j)=\|z_i-z_j\|$. Then the map
--   $$
--   a\mapsto(\varphi_{ij}(a))_{i,j}
--   $$
--   is injective on $K$.
--
--   Countably many functionals separate the points of $K$, which makes the weak topology on $K$ metrizable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/WeakMetric.lean#L44-L90

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric

open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace NormedSpace
open scoped Pointwise
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.ReflexiveFixedPoints.pairNormingFunctional_separates {K : Set X} (z : ℕ → K)
    (hz : DenseRange z) :
    Function.Injective (fun a : K => fun ij => pairNormingFunctional z ij a) := by sorry
