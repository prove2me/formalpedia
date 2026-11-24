-- Prove2me | Theorems.Thm_GlobalTheory_SplitUnitary_Model_isQuad_isHerm_continuous_resEtaPow
-- name    : GlobalTheory.SplitUnitary.Model.isQuad_isHerm_continuous_resEtaPow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:13:10.621797+00:00
-- url     : https://prove2.me/theorems/6226089e-137b-49de-bd6c-ced79db1ba9c
-- title:
--   Model: is Quad is Herm continuous res Eta Pow
-- statement:
--   The Model construction uses the is Quad is Herm continuous res Eta Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ConclRankZeroRight.lean#L28-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ConclRankZeroRight.lean#L28-L46

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

theorem GlobalTheory.SplitUnitary.Model.isQuad_isHerm_continuous_resEtaPow (K : Type) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] (k : ℕ) :
    ∃ (_ : TopologicalSpace (QuadraticAlgebra K d 0)) (_ : IsModuleTopology K (QuadraticAlgebra K d 0))
      (c : QuadraticAlgebra K d 0 →ₐ[K] QuadraticAlgebra K d 0) (δ : QuadraticAlgebra K d 0)
      (Q : Matrix (Fin (2 * k)) (Fin (2 * k)) (QuadraticAlgebra K d 0)) (ψ : AddChar K ℂ)
      (χ : (QuadraticAlgebra K d 0)ˣ →* Circle),
      IsQuad c δ ∧ IsHerm c Q ∧ Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ψ ≠ 1 ∧ Continuous χ ∧
        ResEtaPow (R := K) ⊥ χ (Fintype.card (Fin (2 * k))) := by sorry
