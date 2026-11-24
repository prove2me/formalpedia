-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_eq_one_of_forall_pow_near
-- name    : GlobalTheory.WeilM.eq_one_of_forall_pow_near
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:49.6674+00:00
-- url     : https://prove2.me/theorems/e5d828a2-2ffe-48fc-a223-6652885ba7ef
-- title:
--   Weil M: eq one of forall pow near
-- statement:
--   The Weil M construction uses the eq one of forall pow near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocallyConstantAddChar.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocallyConstantAddChar.lean#L59-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormPowTwoPowSubOneGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise
open GlobalTheory GlobalTheory.WeilM

theorem GlobalTheory.WeilM.eq_one_of_forall_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by sorry
