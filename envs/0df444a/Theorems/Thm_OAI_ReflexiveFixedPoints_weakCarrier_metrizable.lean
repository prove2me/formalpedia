-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_weakCarrier_metrizable
-- name    : OAI.ReflexiveFixedPoints.weakCarrier_metrizable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:04:27.195758+00:00
-- url     : https://prove2.me/theorems/e30cb929-63a5-432f-afba-4c64fa79cd6e
-- title:
--   The weak topology on a separable weakly compact set is metrizable
-- statement:
--   Let $K$ be a separable subset of a real normed space $X$ that is weakly compact. Then $K$ with the weak topology of $X$ is
--   $$
--   \text{metrizable}.
--   $$
--
--   No separability of $X$ or of its dual is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/WeakMetric.lean#L92-L119

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

theorem OAI.ReflexiveFixedPoints.weakCarrier_metrizable {K : Set X} (hsep : IsSeparable K)
    (hcompact : WeaklyCompact K) : MetrizableSpace (WeakCarrier K) := by sorry
