-- Prove2me | Theorems.Thm_GlobalTheory_schur_scalar_bound
-- name    : GlobalTheory.schur_scalar_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:20:17.706705+00:00
-- url     : https://prove2.me/theorems/7429fb2a-6a2e-439b-90dd-273e3280b129
-- title:
--   Global Theory: schur scalar bound
-- statement:
--   The Global Theory construction uses the schur scalar bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SchurComplementBlockQuadraticLowerBound.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SchurComplementBlockQuadraticLowerBound.lean#L7-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SchurComplementBlockQuadraticLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.schur_scalar_bound (u w C₀ c₀ : ℝ) (hC : 0 ≤ C₀) (hc : 0 < c₀) :
    u ^ 2 + w ^ 2 ≤ (1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀) *
      ((1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2) := by sorry
