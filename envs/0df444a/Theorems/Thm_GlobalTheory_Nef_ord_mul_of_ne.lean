-- Prove2me | Theorems.Thm_GlobalTheory_Nef_ord_mul_of_ne
-- name    : GlobalTheory.Nef.ord_mul_of_ne
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:07:10.985409+00:00
-- url     : https://prove2.me/theorems/adf4d3b2-4f3e-4b17-8677-2d267a5a16d4
-- title:
--   Nef: ord mul of ne
-- statement:
--   The Nef construction uses the ord mul of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdmissibleDegreeTwistFamilyAtPlaceByScalar.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdmissibleDegreeTwistFamilyAtPlaceByScalar.lean#L14-L18

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdmissibleDegreeTwistFamilyAtPlaceByScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.ord_mul_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : ord v (x * y) = ord v x + ord v y := by sorry
