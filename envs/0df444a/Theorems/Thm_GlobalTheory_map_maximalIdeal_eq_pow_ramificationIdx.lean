-- Prove2me | Theorems.Thm_GlobalTheory_map_maximalIdeal_eq_pow_ramificationIdx
-- name    : GlobalTheory.map_maximalIdeal_eq_pow_ramificationIdx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:13.176803+00:00
-- url     : https://prove2.me/theorems/348caf3e-51ea-4109-94ce-a6e071e0decf
-- title:
--   Global Theory: map maximal Ideal eq pow ramification Idx
-- statement:
--   The Global Theory construction uses the map maximal Ideal eq pow ramification Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L89-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L89-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open IsDiscreteValuationRing hiding maximalIdeal
variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]
variable [IsLocalHom (algebraMap R S)]

theorem GlobalTheory.map_maximalIdeal_eq_pow_ramificationIdx :
    (maximalIdeal R).map (algebraMap R S) =
      maximalIdeal S ^ ((maximalIdeal S).ramificationIdx R) := by sorry
