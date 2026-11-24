-- Prove2me | Theorems.Thm_GlobalTheory_IntersectionSymm_height_one_or_eq_max
-- name    : GlobalTheory.IntersectionSymm.height_one_or_eq_max
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:43.675002+00:00
-- url     : https://prove2.me/theorems/93511c90-e5ce-49ff-9e75-a0d9aae27c48
-- title:
--   Intersection Symm: height one or eq max
-- statement:
--   The Intersection Symm construction uses the height one or eq max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L64-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L64-L78

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

theorem GlobalTheory.IntersectionSymm.height_one_or_eq_max {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (hA : ringKrullDim A = 2) (p : Ideal A) [hp : p.IsPrime] (h0 : p ≠ ⊥) :
    p.height = 1 ∨ p = maximalIdeal A := by sorry
