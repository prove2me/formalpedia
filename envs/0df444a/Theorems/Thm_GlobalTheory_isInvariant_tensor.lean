-- Prove2me | Theorems.Thm_GlobalTheory_isInvariant_tensor
-- name    : GlobalTheory.isInvariant_tensor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:03.583809+00:00
-- url     : https://prove2.me/theorems/65cdb77d-b1ab-53ab-b30c-89be79840d94
-- title:
--   Global Theory: is Invariant tensor
-- statement:
--   The Global Theory construction uses the is Invariant tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L390-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L390-L396

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (G : Type*) [Group G]
variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

theorem GlobalTheory.isInvariant_tensor [Finite G] [Module.Flat R S] [Algebra.IsInvariant R A G] :
    letI := tensorMulSemiringAction G R S A
    Algebra.IsInvariant S (S ⊗[R] A) G := by sorry
