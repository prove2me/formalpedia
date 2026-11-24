-- Prove2me | Theorems.Thm_GlobalTheory_HerbrandLength_eq_of_le
-- name    : GlobalTheory.HerbrandLength.eq_of_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:19:47.350488+00:00
-- url     : https://prove2.me/theorems/94505a76-8cfc-4d12-a705-d50cb7865ac3
-- title:
--   Herbrand Length: eq of le
-- statement:
--   The Herbrand Length construction uses the eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthCokerLsmulEqLengthKerAddSum.lean#L130-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthCokerLsmulEqLengthKerAddSum.lean#L130-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HerbrandLength
open IsLocalRing
variable {A : Type} [CommRing A]

theorem GlobalTheory.HerbrandLength.eq_of_le [IsLocalRing A] (p q : PrimeSpectrum A) (hp : ringKrullDim (A ⧸ p.asIdeal) = 1)
    (hq : ringKrullDim (A ⧸ q.asIdeal) = 1) (hle : p.asIdeal ≤ q.asIdeal) : p = q := by sorry
