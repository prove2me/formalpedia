-- Prove2me | Theorems.Thm_OAI_RuledApproximation_compact_cut_integral
-- name    : OAI.RuledApproximation.compact_cut_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:49:20.213686+00:00
-- url     : https://prove2.me/theorems/95db24fb-cd8d-41b8-b26c-d9c92776e5be
-- title:
--   Cutting a compact set along an open set with null frontier splits integrals additively
-- statement:
--   Let $K\subseteq\mathbb{R}^2$ be compact, let $O\subseteq\mathbb{R}^2$ be open with Lebesgue-null frontier, $|\partial O|=0$, and let $F:\mathbb{R}^2\to\mathbb{R}$ be Lebesgue integrable on $K$. Then:
--
--   1. $K\cap\overline O$ and $K\setminus O$ are compact;
--   2. $K=(K\cap\overline O)\cup(K\setminus O)$;
--   3. the integral of $F$ over $K$ splits along the cut:
--   $$
--   \int_KF=\int_{K\cap\overline O}F+\int_{K\setminus O}F.
--   $$
--
--   The two pieces may overlap, but only inside $\partial O$, which is null; the frontier of $K$ itself may have positive measure. This is what allows local cylinder covers over finitely many patches to be glued with an exactly additive cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/HyperbolicCover.lean#L94-L122

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.compact_cut_integral {K O : Set Plane} (hK : IsCompact K) (hO : IsOpen O)
    (hnull : volume (frontier O) = 0) {F : Plane → ℝ} (hF : IntegrableOn F K) :
    IsCompact (K ∩ closure O) ∧ IsCompact (K \ O) ∧
    K = (K ∩ closure O) ∪ (K \ O) ∧
    (∫ x in K, F x) = (∫ x in K ∩ closure O, F x) + (∫ x in K \ O, F x) := by sorry
