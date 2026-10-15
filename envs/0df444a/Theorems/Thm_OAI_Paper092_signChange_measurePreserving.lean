-- Prove2me | Theorems.Thm_OAI_Paper092_signChange_measurePreserving
-- name    : OAI.Paper092.signChange_measurePreserving
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:16:27.534792+00:00
-- url     : https://prove2.me/theorems/029c8abd-c769-49ce-bc34-83cf49c2effd
-- title:
--   Flipping the signs of some coordinates preserves Lebesgue measure on $\mathbb{R}^n$
-- statement:
--   Let $n\in\mathbb{N}$, let $\lambda^n$ be Lebesgue measure on $\mathbb{R}^n$, and let $s=(s_1,\dots,s_n)\in\{\mathrm{true},\mathrm{false}\}^n$ be a sign pattern. Define $\sigma_s:\mathbb{R}^n\to\mathbb{R}^n$ by
--
--   $$(\sigma_s x)_i=\begin{cases}x_i, & s_i=\mathrm{true},\\ -x_i, & s_i=\mathrm{false}.\end{cases}$$
--
--   Then $\sigma_s$ is measurable and measure preserving: $(\sigma_s)_*\lambda^n=\lambda^n$, i.e. $\lambda^n(\sigma_s^{-1}(A))=\lambda^n(A)$ for every measurable $A\subseteq\mathbb{R}^n$.
--
--   The $2^n$ maps $\sigma_s$ are exactly the compositions of reflections in coordinate hyperplanes. They move the coordinate simplex $\{x:\ x_i\ge0,\ \sum_ix_i\le1\}$ into each of the $2^n$ orthants without changing its volume, which is the key step in computing the volume $1/n!$ of the standard simplex from the volume of the cross-polytope.
--
--   **Formalization Note** The statement is `MeasurePreserving (signChange s) volume volume` on the function space `Fin n → ℝ` with its product Lebesgue measure; `MeasurePreserving` bundles measurability of the map with the equality of the push-forward measure and `volume`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/SimplexVolume.lean#L42-L55

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

theorem OAI.Paper092.signChange_measurePreserving {n : ℕ} (s : Fin n → Bool) :
    MeasurePreserving (signChange s) volume volume := by sorry
