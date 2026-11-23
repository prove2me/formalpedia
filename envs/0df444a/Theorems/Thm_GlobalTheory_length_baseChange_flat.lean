-- Prove2me | Theorems.Thm_GlobalTheory_length_baseChange_flat
-- name    : GlobalTheory.length_baseChange_flat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:07.10517+00:00
-- url     : https://prove2.me/theorems/53d7bfcc-431b-4dc8-b0eb-88930c2a25c4
-- title:
--   Global Theory: length base Change flat
-- statement:
--   The Global Theory construction uses the length base Change flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean#L47-L50

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
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
  (X : Type*) [AddCommGroup X] [Module R X]

theorem GlobalTheory.length_baseChange_flat :
    Module.length S (S ⊗[R] X) =
      Module.length R X * Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by sorry
