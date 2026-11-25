-- Prove2me | Theorems.Thm_GlobalTheory_discr_mul_left_of_basis
-- name    : GlobalTheory.discr_mul_left_of_basis
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:48.433311+00:00
-- url     : https://prove2.me/theorems/76623a5e-657d-54d4-99dd-84ccaa3436cc
-- title:
--   Global Theory: discr mul left of basis
-- statement:
--   The Global Theory construction uses the discr mul left of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L26-L29

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

theorem GlobalTheory.discr_mul_left_of_basis (e : Basis ι R S) (u : S) (v : ι → S) :
    Algebra.discr R (fun i => u * v i) = Algebra.norm R u ^ 2 * Algebra.discr R v := by sorry
