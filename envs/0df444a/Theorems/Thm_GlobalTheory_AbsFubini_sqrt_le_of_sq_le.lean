-- Prove2me | Theorems.Thm_GlobalTheory_AbsFubini_sqrt_le_of_sq_le
-- name    : GlobalTheory.AbsFubini.sqrt_le_of_sq_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:54:09.891608+00:00
-- url     : https://prove2.me/theorems/87d8bafe-ad09-4f39-8930-8f198ed86555
-- title:
--   Abs Fubini: sqrt le of sq le
-- statement:
--   The Abs Fubini construction uses the sqrt le of sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IntegralKernelLiftsFubiniSigmaFinite.lean#L17-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralKernelLiftsFubiniSigmaFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ENNReal
open GlobalTheory GlobalTheory.AbsFubini
variable {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν : Measure Y} [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]

theorem GlobalTheory.AbsFubini.sqrt_le_of_sq_le {I N : ℝ≥0∞} (h : I ≤ N ^ 2) : I ^ (1 / (2:ℝ)) ≤ N := by sorry
