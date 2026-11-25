-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_coeff_le_one
-- name    : GroundTheory.PAdicHodge.norm_coeff_le_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:23.088794+00:00
-- url     : https://prove2.me/theorems/158e9398-8e12-4d8f-978f-fbf6a8a75b7a
-- title:
--   PAdic Hodge: norm coeff le one
-- statement:
--   The PAdic Hodge construction uses the norm coeff le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L111-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L111-L127

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

theorem GroundTheory.PAdicHodge.norm_coeff_le_one {c : ℚ_[p]} {i : ℕ} (hi : i < Nat.totient (p ^ (k + 1)))
    (h : ‖c‖ * ‖ζ - 1‖ ^ i ≤ 1) : ‖c‖ ≤ 1 := by sorry
