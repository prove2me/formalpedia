-- Prove2me | Theorems.Thm_GlobalTheory_isogeny_numerator_coeff_norm_le_one
-- name    : GlobalTheory.isogeny_numerator_coeff_norm_le_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:46.940385+00:00
-- url     : https://prove2.me/theorems/0c1d5ab5-f436-4f3c-936f-5f523a869780
-- title:
--   Global Theory: isogeny numerator coeff norm le one
-- statement:
--   The Global Theory construction uses the isogeny numerator coeff norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsogenyNumeratorCoeffNormLeOne.lean#L25-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsogenyNumeratorCoeffNormLeOne.lean#L25-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsogenyNumeratorCoeffNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.isogeny_numerator_coeff_norm_le_one :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (A B A' B' : K) (n h : K[X]),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖A'‖ ≤ 1 → ‖B'‖ ≤ 1 → (∀ i, ‖h.coeff i‖ ≤ 1) →
      (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2
        = n ^ 3 + C A' * n * h ^ 4 + C B' * h ^ 6 → ∀ i, ‖n.coeff i‖ ≤ 1 := by sorry
