-- Prove2me | Theorems.Thm_GlobalTheory_two_mul_length_le_addVal_discr
-- name    : GlobalTheory.two_mul_length_le_addVal_discr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:16.763578+00:00
-- url     : https://prove2.me/theorems/28618199-4768-4f41-9137-c904a790afb3
-- title:
--   Global Theory: two mul length le add Val discr
-- statement:
--   The Global Theory construction uses the two mul length le add Val discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L39-L42

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

theorem GlobalTheory.two_mul_length_le_addVal_discr (e : Basis ι R S) (v : ι → S) :
    2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) ≤ addVal R (Algebra.discr R v) := by sorry
