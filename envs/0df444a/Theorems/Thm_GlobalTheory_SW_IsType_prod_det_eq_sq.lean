-- Prove2me | Theorems.Thm_GlobalTheory_SW_IsType_prod_det_eq_sq
-- name    : GlobalTheory.SW.IsType.prod_det_eq_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:15.660311+00:00
-- url     : https://prove2.me/theorems/84c29056-1a67-4826-890b-0a74679b9e69
-- title:
--   Is Type: prod det eq sq
-- statement:
--   The Is Type construction uses the prod det eq sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L172-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L172-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.IsType.prod_det_eq_sq {E m n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype m]
    [Fintype n] [DecidableEq n] {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (W : Matrix n m E) :
    ∏ σ : E →+* ℂ, (W.map σ * (W.map σ)ᴴ).det =
      (((∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re) ^ 2 : ℝ) : ℂ) := by sorry
