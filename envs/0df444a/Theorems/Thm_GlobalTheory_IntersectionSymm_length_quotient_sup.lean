-- Prove2me | Theorems.Thm_GlobalTheory_IntersectionSymm_length_quotient_sup
-- name    : GlobalTheory.IntersectionSymm.length_quotient_sup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:08.269961+00:00
-- url     : https://prove2.me/theorems/e8d8e1ed-5152-489e-b0e1-60a5b3ee3577
-- title:
--   Intersection Symm: length quotient sup
-- statement:
--   The Intersection Symm construction uses the length quotient sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L99-L104

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

theorem GlobalTheory.IntersectionSymm.length_quotient_sup {A : Type} [CommRing A] (p : Ideal A) (b : A) :
    Module.length A (A ⧸ (p ⊔ Ideal.span {b})) =
      Module.length (A ⧸ p) ((A ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p b}) := by sorry
