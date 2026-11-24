-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_pow_of_ratio_of_torsionFree
-- name    : GlobalTheory.exists_mem_pow_of_ratio_of_torsionFree
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:21.564492+00:00
-- url     : https://prove2.me/theorems/72aa1329-ff2c-4834-9ad2-1b8bf75b2767
-- title:
--   Global Theory: exists mem pow of ratio of torsion Free
-- statement:
--   The Global Theory construction uses the exists mem pow of ratio of torsion Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMemPowOfRatioOfTorsionFree.lean#L5-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMemPowOfRatioOfTorsionFree.lean#L5-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMemPowOfRatioOfTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_mem_pow_of_ratio_of_torsionFree :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O]
      (io : V →+* O), (∀ v : V, v ≠ 0 → ∀ x : O, io v * x = 0 → x = 0) →
      ∀ (f h : O) (p q : V) (m n : ℕ), q ≠ 0 → io q * f = io p * h →
      f ∈ (IsLocalRing.maximalIdeal V ^ (m + n)).map io →
      h ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map io →
      ∃ r ∈ IsLocalRing.maximalIdeal V ^ n, p = r * q := by sorry
