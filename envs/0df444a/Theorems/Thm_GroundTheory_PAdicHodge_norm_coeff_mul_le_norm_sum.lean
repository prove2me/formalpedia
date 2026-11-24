-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_coeff_mul_le_norm_sum
-- name    : GroundTheory.PAdicHodge.norm_coeff_mul_le_norm_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:09.590015+00:00
-- url     : https://prove2.me/theorems/62823c36-6b23-4572-a237-8dd2baae0311
-- title:
--   PAdic Hodge: norm coeff mul le norm sum
-- statement:
--   The PAdic Hodge construction uses the norm coeff mul le norm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L74-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L74-L109

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]
variable {k : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
include hζ

theorem GroundTheory.PAdicHodge.norm_coeff_mul_le_norm_sum (a : ℕ → ℚ_[p]) :
    ∀ i ∈ Finset.range (Nat.totient (p ^ (k + 1))),
      ‖a i‖ * ‖ζ - 1‖ ^ i ≤ ‖∑ j ∈ Finset.range (Nat.totient (p ^ (k + 1))),
        algebraMap ℚ_[p] (PadicAlgCl p) (a j) * (ζ - 1) ^ j‖ := by sorry
