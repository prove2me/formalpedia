-- Prove2me | Theorems.Thm_GlobalTheory_SW_SiegelSum_summable_norm_thetaTerm
-- name    : GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:57.197294+00:00
-- url     : https://prove2.me/theorems/66e77c14-b562-41d3-904a-edda7d4a03f1
-- title:
--   Siegel Sum: summable norm theta Term
-- statement:
--   The Siegel Sum construction uses the summable norm theta Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableNormSiegelThetaSeriesTerms.lean#L116-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableNormSiegelThetaSeriesTerms.lean#L116-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelSum

theorem GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ : Matrix κ ι ℚ → ℂ), IsSB φ → ∀ τ ∈ Siegel ι, ∀ ζ : κ → ι → ℂ, Summable fun x : Matrix κ ι ℚ => ‖φ x * cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))‖ := by sorry
