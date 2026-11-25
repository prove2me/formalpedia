-- Prove2me | Theorems.Thm_GlobalTheory_Nef_ord_zpow_of_ne
-- name    : GlobalTheory.Nef.ord_zpow_of_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:06:51.33515+00:00
-- url     : https://prove2.me/theorems/d11f4a7d-ccc5-48f3-b29e-765c1617da2c
-- title:
--   Nef: ord zpow of ne
-- statement:
--   The Nef construction uses the ord zpow of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdmissibleDegreeTwistFamilyAtPlaceByScalar.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdmissibleDegreeTwistFamilyAtPlaceByScalar.lean#L20-L25

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

theorem GlobalTheory.Nef.ord_zpow_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) {x : F} (hx : x ≠ 0)
    (m : ℤ) : ord v (x ^ m) = m * ord v x := by sorry
