-- Prove2me | Theorems.Thm_GlobalTheory_HeckeLat_periodic_bound_summable_norm
-- name    : GlobalTheory.HeckeLat.periodic_bound_summable_norm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:03:56.902537+00:00
-- url     : https://prove2.me/theorems/8d923269-6583-457b-9434-17b80a852823
-- title:
--   Hecke Lat: periodic bound summable norm
-- statement:
--   The Hecke Lat construction uses the periodic bound summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodicBoundedGaussianSummableCmType.lean#L112-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodicBoundedGaussianSummableCmType.lean#L112-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeLat
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

theorem GlobalTheory.HeckeLat.periodic_bound_summable_norm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ),
      M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K =>
        ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧
      ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by sorry
