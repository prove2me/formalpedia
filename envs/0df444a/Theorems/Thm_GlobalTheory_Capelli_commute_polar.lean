-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_commute_polar
-- name    : GlobalTheory.Capelli.commute_polar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:57.134426+00:00
-- url     : https://prove2.me/theorems/c01d5a0b-5da2-43e5-8de6-e82e8a24a874
-- title:
--   Capelli: commute polar
-- statement:
--   The Capelli construction uses the commute polar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L95-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
variable {I J I' J' : Type*}

theorem GlobalTheory.Capelli.commute_polar {u v w s : σ} (h₁ : v ≠ w) (h₂ : s ≠ u) :
    Commute (polar K u v) (polar K w s) := by sorry
