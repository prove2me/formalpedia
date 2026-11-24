-- Prove2me | Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- name    : GlobalTheory.Wick.dividedContraction_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:51.699205+00:00
-- url     : https://prove2.me/theorems/1a63aedf-fde2-4ceb-add5-0550587c982e
-- title:
--   Wick: divided Contraction one
-- statement:
--   The Wick construction uses the divided Contraction one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L413-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L413-L414

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Wick
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}
variable [Fintype κ]
variable [Fintype ι]

theorem GlobalTheory.Wick.dividedContraction_one (γ : ι → κ → R) : dividedContraction γ 1 = contraction γ := by sorry
