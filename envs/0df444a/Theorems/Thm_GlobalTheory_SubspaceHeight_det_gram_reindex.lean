-- Prove2me | Theorems.Thm_GlobalTheory_SubspaceHeight_det_gram_reindex
-- name    : GlobalTheory.SubspaceHeight.det_gram_reindex
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:57.9923+00:00
-- url     : https://prove2.me/theorems/a0aefa3a-57ab-446e-bcce-46fe90a60910
-- title:
--   Subspace Height: det gram reindex
-- statement:
--   The Subspace Height construction uses the det gram reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsSubspaceHeightGramDeterminant.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsSubspaceHeightGramDeterminant.lean#L14-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetDivIndexEqOfSpanEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSubspaceHeightGramDeterminant
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
open GlobalTheory GlobalTheory.SubspaceHeight
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SubspaceHeight.det_gram_reindex {r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) (A : Matrix (Fin r) (Fin r) ℂ) (f : ι → Fin r → ℂ) :
    ((A * (Matrix.of fun k a => f (e a) k))ᴴ * (A * (Matrix.of fun k a => f (e a) k))).det =
      ((A * (Matrix.of fun k a => f a k))ᴴ * (A * (Matrix.of fun k a => f a k))).det := by sorry
