-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_zpow_mul_pow_sub_one_pow
-- name    : GroundTheory.PAdicHodge.norm_zpow_mul_pow_sub_one_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:22.072752+00:00
-- url     : https://prove2.me/theorems/2b469302-8683-48ad-9a96-695ff148d237
-- title:
--   PAdic Hodge: norm zpow mul pow sub one pow
-- statement:
--   The PAdic Hodge construction uses the norm zpow mul pow sub one pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L65-L72

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

theorem GroundTheory.PAdicHodge.norm_zpow_mul_pow_sub_one_pow (z : ℤ) (m : ℕ) :
    ((p : ℝ) ^ z * ‖ζ - 1‖ ^ m) ^ Nat.totient (p ^ (k + 1)) =
      (p : ℝ) ^ (z * Nat.totient (p ^ (k + 1)) - m) := by sorry
