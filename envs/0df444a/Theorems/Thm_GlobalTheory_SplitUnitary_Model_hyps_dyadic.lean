-- Prove2me | Theorems.Thm_GlobalTheory_SplitUnitary_Model_hyps_dyadic
-- name    : GlobalTheory.SplitUnitary.Model.hyps_dyadic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:34:01.715186+00:00
-- url     : https://prove2.me/theorems/db970fc8-aa2a-56b2-ab80-f704bb2b333f
-- title:
--   Model: hyps dyadic
-- statement:
--   The Model construction uses the hyps dyadic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ConclRankZeroRight.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ConclRankZeroRight.lean#L48-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ConclRankZeroRight
import Theorems.Thm_GlobalTheory_HermLocal_Model_conjSqrt_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.SplitUnitary GlobalTheory.SplitUnitary.Model
open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.HermLocal.Model (conjSqrt conjSqrt_apply)

theorem GlobalTheory.SplitUnitary.Model.hyps_dyadic : ∃ (_ : IsNonarchimedeanLocalField ℚ_[2]) (_ : TopologicalSpace (QuadraticAlgebra ℚ_[2] 2 0))
      (_ : IsModuleTopology ℚ_[2] (QuadraticAlgebra ℚ_[2] 2 0))
      (c : QuadraticAlgebra ℚ_[2] 2 0 →ₐ[ℚ_[2]] QuadraticAlgebra ℚ_[2] 2 0) (δ : QuadraticAlgebra ℚ_[2] 2 0)
      (Q : Matrix (Fin (2 * 1)) (Fin (2 * 1)) (QuadraticAlgebra ℚ_[2] 2 0)) (ψ : AddChar ℚ_[2] ℂ)
      (χ : (QuadraticAlgebra ℚ_[2] 2 0)ˣ →* Circle),
      IsQuad c δ ∧ IsHerm c Q ∧ Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ψ ≠ 1 ∧ Continuous χ ∧
        ResEtaPow (R := ℚ_[2]) ⊥ χ (Fintype.card (Fin (2 * 1))) := by sorry
