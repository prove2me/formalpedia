-- Prove2me | Theorems.Thm_GlobalTheory_discr_eq_det_toMatrix_sq_mul
-- name    : GlobalTheory.discr_eq_det_toMatrix_sq_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:18.324497+00:00
-- url     : https://prove2.me/theorems/85a9a7fd-47c2-4b3a-9356-190450de4172
-- title:
--   Global Theory: discr eq det to Matrix sq mul
-- statement:
--   The Global Theory construction uses the discr eq det to Matrix sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L13-L15

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

theorem GlobalTheory.discr_eq_det_toMatrix_sq_mul (e : Basis ι R S) (v : ι → S) :
    Algebra.discr R v = (e.toMatrix v).det ^ 2 * Algebra.discr R e := by sorry
