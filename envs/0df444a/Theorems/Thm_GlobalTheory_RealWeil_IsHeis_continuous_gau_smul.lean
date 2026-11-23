-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous_gau_smul
-- name    : GlobalTheory.RealWeil.IsHeis.continuous_gau_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:35.588201+00:00
-- url     : https://prove2.me/theorems/afff5491-6ecb-443f-bb8c-305322fa8879
-- title:
--   Is Heis: continuous gau smul
-- statement:
--   The Is Heis construction uses the continuous gau smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousFourierGau.lean#L97-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousFourierGau.lean#L97-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace B]

theorem GlobalTheory.RealWeil.IsHeis.continuous_gau_smul (h : IsHeis om ρ) (f : B) : Continuous fun u => gau u • ρ u f := by sorry
