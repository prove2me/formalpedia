-- Prove2me | Theorems.Thm_GlobalTheory_addVal_discr_eq_two_mul_length_add
-- name    : GlobalTheory.addVal_discr_eq_two_mul_length_add
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:20.161989+00:00
-- url     : https://prove2.me/theorems/34712958-2e2b-4a8f-bf29-c82a3980dd8b
-- title:
--   Global Theory: add Val discr eq two mul length add
-- statement:
--   The Global Theory construction uses the add Val discr eq two mul length add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L33-L37

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

theorem GlobalTheory.addVal_discr_eq_two_mul_length_add (e : Basis ι R S) (v : ι → S) :
    addVal R (Algebra.discr R v) =
      2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) + addVal R (Algebra.discr R e) := by sorry
