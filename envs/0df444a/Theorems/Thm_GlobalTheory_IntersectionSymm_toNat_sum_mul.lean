-- Prove2me | Theorems.Thm_GlobalTheory_IntersectionSymm_toNat_sum_mul
-- name    : GlobalTheory.IntersectionSymm.toNat_sum_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:20:06.62796+00:00
-- url     : https://prove2.me/theorems/e2772220-1011-4e5b-b6a4-0f6320b594b8
-- title:
--   Intersection Symm: to Nat sum mul
-- statement:
--   The Intersection Symm construction uses the to Nat sum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L184-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L184-L187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.IntersectionSymm

theorem GlobalTheory.IntersectionSymm.toNat_sum_mul {ι : Type} (S : Finset ι) (f g : ι → ℕ∞) (h : ∀ i ∈ S, f i * g i ≠ ⊤) :
    ∑ i ∈ S, (f i).toNat * (g i).toNat = (∑ i ∈ S, f i * g i).toNat := by sorry
