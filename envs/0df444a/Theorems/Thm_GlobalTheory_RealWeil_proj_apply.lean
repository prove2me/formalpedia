-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_proj_apply
-- name    : GlobalTheory.RealWeil.proj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:47.535009+00:00
-- url     : https://prove2.me/theorems/699bb08f-90cf-463a-8857-7c9000cfc5eb
-- title:
--   Real Weil: proj apply
-- statement:
--   The Real Weil construction uses the proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousFourierGau.lean#L115-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousFourierGau.lean#L115-L115

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
omit [CompleteSpace B]

theorem GlobalTheory.RealWeil.proj_apply (h : IsHeis om ρ) (f : B) : proj h f = ∫ u, gau u • ρ u f := by sorry
