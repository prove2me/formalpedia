-- Prove2me | Theorems.Thm_OAI_Paper092_twice_sum_negative_eq_sum_abs
-- name    : OAI.Paper092.twice_sum_negative_eq_sum_abs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:15:59.258455+00:00
-- url     : https://prove2.me/theorems/f8cd8233-7453-4cde-bf47-86a303a4ab41
-- title:
--   For a zero-sum vector, twice the total of its negative parts equals its $\ell^1$ norm
-- statement:
--   Let $\iota$ be a finite index set and let $v\in\mathbb{R}^\iota$ be a real vector whose entries sum to zero, $\sum_{i\in\iota}v_i=0$. Then
--
--   $$2\sum_{i\in\iota:\ v_i<0}(-v_i)=\sum_{i\in\iota}|v_i| .$$
--
--   Equivalently, the negative entries of a zero-sum vector account for exactly half of its $\ell^1$ norm. In the brightness computation, $v$ is the list of velocities of the $d+1$ barycentric coordinates of the standard simplex $T_d$ along a direction $u$, namely $-\sum_i u_i$ and $u_1,\dots,u_d$, which sum to zero; the identity turns the sum over the front facets into the closed form $\tfrac12\bigl(\sum_i|u_i|+|\sum_i u_i|\bigr)$.
--
--   **Formalization Note** The sum on the left runs over the subtype `{i // v i < 0}` of the finite type $\iota$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProjectionCoefficients.lean#L11-L26

import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection

open OAI OAI.Paper092
universe uι
open scoped BigOperators

theorem OAI.Paper092.twice_sum_negative_eq_sum_abs {ι : Type uι} [Fintype ι] (v : ι → ℝ)
    (hv : ∑ i, v i = 0) :
    2 * (∑ i : {i // v i < 0}, -v i.val) = ∑ i, |v i| := by sorry
