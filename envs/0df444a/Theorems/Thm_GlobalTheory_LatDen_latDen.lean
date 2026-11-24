-- Prove2me | Theorems.Thm_GlobalTheory_LatDen_latDen
-- name    : GlobalTheory.LatDen.latDen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:40.526995+00:00
-- url     : https://prove2.me/theorems/ac195c6e-08ff-4512-97b4-9a7c897a7416
-- title:
--   Lat Den: lat Den
-- statement:
--   The Lat Den construction uses the lat Den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LatDen.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LatDen.lean#L13-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatDen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.LatDen
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.LatDen.latDen : (∀ (r : ℕ) (X : Data E r), (∀ v : Fin r → E, ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ X.Λ) ∧ ∃ n : ℕ, 0 < n ∧ ∀ v ∈ X.Λ, ∀ k, IsIntegral ℤ ((n : E) * v k)) := by sorry
