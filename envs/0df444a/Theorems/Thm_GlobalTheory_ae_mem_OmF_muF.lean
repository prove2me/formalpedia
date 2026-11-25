-- Prove2me | Theorems.Thm_GlobalTheory_ae_mem_OmF_muF
-- name    : GlobalTheory.ae_mem_OmF_muF
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:11.928108+00:00
-- url     : https://prove2.me/theorems/5bf912c4-fc7d-57c4-8711-e117a16ced6d
-- title:
--   Global Theory: ae mem Om F mu F
-- statement:
--   The Global Theory construction uses the ae mem Om F mu F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OfRealTsumSqLeTsumDivMulTsum.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OfRealTsumSqLeTsumDivMulTsum.lean#L37-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealTsumSqLeTsumDivMulTsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.ae_mem_OmF_muF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := by sorry
