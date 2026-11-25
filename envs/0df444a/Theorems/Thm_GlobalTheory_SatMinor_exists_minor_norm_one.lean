-- Prove2me | Theorems.Thm_GlobalTheory_SatMinor_exists_minor_norm_one
-- name    : GlobalTheory.SatMinor.exists_minor_norm_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:44:48.56712+00:00
-- url     : https://prove2.me/theorems/638b65a8-51ff-4b34-b64b-ee2b89e19c81
-- title:
--   Sat Minor: exists minor norm one
-- statement:
--   The Sat Minor construction uses the exists minor norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitMinorOfIntegralMatrix.lean#L48-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitMinorOfIntegralMatrix.lean#L48-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitMinorOfIntegralMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SatMinor
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.SatMinor.exists_minor_norm_one : ∀ (p : ℕ) [Fact p.Prime] {κ J : Type} [Fintype κ] [DecidableEq κ] [Fintype J]
    (c : Matrix κ J ℂ_[p]),
    (∀ k i, ‖c k i‖ ≤ 1) →
    (∀ a : κ → ℂ_[p], (∀ i, ‖∑ k, a k * c k i‖ ≤ 1) → ∀ k, ‖a k‖ ≤ 1) →
    ∃ f : κ → J, Function.Injective f ∧ ‖(c.submatrix id f).det‖ = 1 := by sorry
