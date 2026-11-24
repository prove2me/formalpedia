-- Prove2me | Theorems.Thm_GlobalTheory_UnramPushout_isReduced_nontrivial_tensor
-- name    : GlobalTheory.UnramPushout.isReduced_nontrivial_tensor
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:53.034731+00:00
-- url     : https://prove2.me/theorems/f9ea0b63-3b0f-49c8-902d-b7d2ed8aada4
-- title:
--   Unram Pushout: is Reduced nontrivial tensor
-- statement:
--   The Unram Pushout construction uses the is Reduced nontrivial tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalPushoutUnramifiedCharZero.lean#L9-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalPushoutUnramifiedCharZero.lean#L9-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalPushoutUnramifiedCharZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.UnramPushout
open TensorProduct

theorem GlobalTheory.UnramPushout.isReduced_nontrivial_tensor {A k k' : Type} [CommRing A] [Field k] [Field k']
    [Algebra A k] [Algebra A k'] [CharZero k] (P : Ideal A) [P.IsPrime]
    (hk : RingHom.ker (algebraMap A k) = P) (hk' : RingHom.ker (algebraMap A k') = P) :
    IsReduced (k ⊗[A] k') ∧ Nontrivial (k ⊗[A] k') := by sorry
