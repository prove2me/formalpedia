-- Prove2me | Theorems.Thm_GlobalTheory_ProperFromMinimum_bound_of_ineqs
-- name    : GlobalTheory.ProperFromMinimum.bound_of_ineqs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:34.038248+00:00
-- url     : https://prove2.me/theorems/4e83737d-dae7-588a-bd2f-be51e43549ac
-- title:
--   Proper From Minimum: bound of ineqs
-- statement:
--   The Proper From Minimum construction uses the bound of ineqs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/BoundOfIneqs.lean#L11-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/BoundOfIneqs.lean#L11-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_FirstMinimumInvariantContinuousPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModelNefness
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_BoundOfIneqs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open GlobalTheory GlobalTheory.ProperFromMinimum

theorem GlobalTheory.ProperFromMinimum.bound_of_ineqs {K K' c i δ S n p : ℝ} {a : ℕ} (hδ : 0 < δ) (hac : (a : ℝ) * c < i)
    (hS : 0 ≤ S) (h1 : Real.exp (-(2 * c * p)) ≤ K * S) (h2 : n ≤ K' * Real.exp (-(2 * i * p)))
    (h3 : δ * S ^ a ≤ n) : p ≤ K ^ a * K' / δ / (2 * (i - a * c)) := by sorry
