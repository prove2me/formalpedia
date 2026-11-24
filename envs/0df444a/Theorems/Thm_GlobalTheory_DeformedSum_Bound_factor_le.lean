-- Prove2me | Theorems.Thm_GlobalTheory_DeformedSum_Bound_factor_le
-- name    : GlobalTheory.DeformedSum.Bound.factor_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:36:09.553787+00:00
-- url     : https://prove2.me/theorems/7d5ff9fd-111f-4787-9b2b-46fad0d08025
-- title:
--   Bound: factor le
-- statement:
--   The Bound construction uses the factor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DeformedProductDerivativeTermNormLeUniform.lean#L21-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DeformedProductDerivativeTermNormLeUniform.lean#L21-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DeformedSum GlobalTheory.DeformedSum.Bound
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem GlobalTheory.DeformedSum.Bound.factor_le (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (z : I → ℂ) (x : E) (hx : x ≠ 0) (i : I) {r : ℝ} (hr : r < 1)
    (hz : ‖z i‖ ≤ r) :
    ‖((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
        (defCoord φ z x i)⁻¹ ^ (k + m i)‖ ≤
      ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)‖ * ((1 - r)⁻¹) ^ (k + m i) * (‖φ i x‖⁻¹) ^ k := by sorry
