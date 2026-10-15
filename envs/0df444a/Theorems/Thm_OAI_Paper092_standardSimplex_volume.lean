-- Prove2me | Theorems.Thm_OAI_Paper092_standardSimplex_volume
-- name    : OAI.Paper092.standardSimplex_volume
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:16:56.309251+00:00
-- url     : https://prove2.me/theorems/a65eafbd-cdab-4af5-aad8-33e5c527a145
-- title:
--   The standard simplex in $\mathbb{R}^n$ has volume $1/n!$
-- statement:
--   Let $n\in\mathbb{N}$ and let $T_n=\operatorname{conv}\{0,e_1,\dots,e_n\}$ be the standard simplex in Euclidean space $\mathbb{R}^n$, the convex hull of the origin and the standard basis vectors. Its $n$-dimensional Lebesgue measure is
--
--   $$\operatorname{vol}_n(T_n)=\frac{1}{n!}.$$
--
--   This classical formula fixes the volume normalization in all computations with simplices. In particular it gives $\operatorname{vol}(T_{10}\times T_{10})=(1/10!)^2$, the quantity whose $19$-th power appears in the denominator of the normalized projection volume $\operatorname{vol}(\Pi K)/\operatorname{vol}(K)^{19}$ of the product body $K=T_{10}\times T_{10}$.
--
--   **Formalization Note** The statement is an equality of extended nonnegative reals, `volume (standardSimplex n) = ENNReal.ofReal (1 / (Nat.factorial n : ℝ))`, where `volume` on `EuclideanSpace ℝ (Fin n)` is Lebesgue measure. The case $n=0$ is included: $T_0$ is the single point of $\mathbb{R}^0$, of measure $1=1/0!$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/SimplexVolume.lean#L134-L147

import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume

open OAI OAI.Paper092
open Set MeasureTheory
open scoped BigOperators ENNReal

theorem OAI.Paper092.standardSimplex_volume (n : ℕ) :
    volume (standardSimplex n) = ENNReal.ofReal (1 / (Nat.factorial n : ℝ)) := by sorry
