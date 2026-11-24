-- Prove2me | Theorems.Thm_GlobalTheory_CharFamily_seminorm_mul_le
-- name    : GlobalTheory.CharFamily.seminorm_mul_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:08:15.104904+00:00
-- url     : https://prove2.me/theorems/605f70fe-c9b9-41d4-babb-5d3c99012be7
-- title:
--   Char Family: seminorm mul le
-- statement:
--   The Char Family construction uses the seminorm mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFamilyPhaseBound.lean#L10-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFamilyPhaseBound.lean#L10-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
open GlobalTheory GlobalTheory.CharFamily
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem GlobalTheory.CharFamily.seminorm_mul_le (c : E → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (h g : SchwartzMap E ℂ)
    (hg : ∀ x, g x = c x * h x) (k n m : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hcb : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i c x‖ ≤ M * (1 + ‖x‖) ^ m) :
    SchwartzMap.seminorm ℂ k n g ≤ 2 ^ n * M *
      (2 ^ (k + m) * ((Finset.Iic (k + m, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) h) := by sorry
