-- Prove2me | Theorems.Thm_GlobalTheory_discr_eq_basis_det_sq_mul
-- name    : GlobalTheory.discr_eq_basis_det_sq_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:45.339798+00:00
-- url     : https://prove2.me/theorems/61be229b-f84a-4267-81b3-e4d38d601bbd
-- title:
--   Global Theory: discr eq basis det sq mul
-- statement:
--   The Global Theory construction uses the discr eq basis det sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L17-L19

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

theorem GlobalTheory.discr_eq_basis_det_sq_mul (e : Basis ι R S) (v : ι → S) :
    Algebra.discr R v = e.det v ^ 2 * Algebra.discr R e := by sorry
