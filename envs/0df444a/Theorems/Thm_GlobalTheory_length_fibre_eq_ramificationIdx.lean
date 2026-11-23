-- Prove2me | Theorems.Thm_GlobalTheory_length_fibre_eq_ramificationIdx
-- name    : GlobalTheory.length_fibre_eq_ramificationIdx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:03.919171+00:00
-- url     : https://prove2.me/theorems/60a2d25b-eecc-40a1-aaad-3a05a8c67d5d
-- title:
--   Global Theory: length fibre eq ramification Idx
-- statement:
--   The Global Theory construction uses the length fibre eq ramification Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L102-L106

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

theorem GlobalTheory.length_fibre_eq_ramificationIdx :
    Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) =
      ((maximalIdeal S).ramificationIdx R : ℕ) := by sorry
