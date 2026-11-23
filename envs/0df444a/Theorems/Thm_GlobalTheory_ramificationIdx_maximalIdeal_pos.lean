-- Prove2me | Theorems.Thm_GlobalTheory_ramificationIdx_maximalIdeal_pos
-- name    : GlobalTheory.ramificationIdx_maximalIdeal_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:35.220368+00:00
-- url     : https://prove2.me/theorems/e530ec6f-1b4a-4f08-899d-0b28efcafbe6
-- title:
--   Global Theory: ramification Idx maximal Ideal pos
-- statement:
--   The Global Theory construction uses the ramification Idx maximal Ideal pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L108-L112

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

theorem GlobalTheory.ramificationIdx_maximalIdeal_pos : 0 < (maximalIdeal S).ramificationIdx R := by sorry
