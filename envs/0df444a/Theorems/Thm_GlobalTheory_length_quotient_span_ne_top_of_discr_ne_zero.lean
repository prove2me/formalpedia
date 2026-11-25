-- Prove2me | Theorems.Thm_GlobalTheory_length_quotient_span_ne_top_of_discr_ne_zero
-- name    : GlobalTheory.length_quotient_span_ne_top_of_discr_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:15.417869+00:00
-- url     : https://prove2.me/theorems/faad82e9-6785-4103-93b7-6cef8936ba19
-- title:
--   Global Theory: length quotient span ne top of discr ne zero
-- statement:
--   The Global Theory construction uses the length quotient span ne top of discr ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L50-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]
variable [IsDomain R] [IsDiscreteValuationRing R]

theorem GlobalTheory.length_quotient_span_ne_top_of_discr_ne_zero (e : Basis ι R S) {v : ι → S}
    (hv : Algebra.discr R v ≠ 0) :
    Module.length R (S ⧸ Submodule.span R (Set.range v)) ≠ ⊤ := by sorry
