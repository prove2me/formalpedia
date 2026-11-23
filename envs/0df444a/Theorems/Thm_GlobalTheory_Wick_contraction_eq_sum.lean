-- Prove2me | Theorems.Thm_GlobalTheory_Wick_contraction_eq_sum
-- name    : GlobalTheory.Wick.contraction_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:13.215094+00:00
-- url     : https://prove2.me/theorems/4310fca9-5c20-48ca-8edd-1b881eb3fe45
-- title:
--   Wick: contraction eq sum
-- statement:
--   The Wick construction uses the contraction eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L268-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L268-L271

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

theorem GlobalTheory.Wick.contraction_eq_sum (γ : ι → κ → R) :
    contraction γ = ∑ i, (pderiv (Sum.inl i)).toLinearMap * rowContraction γ i := by sorry
