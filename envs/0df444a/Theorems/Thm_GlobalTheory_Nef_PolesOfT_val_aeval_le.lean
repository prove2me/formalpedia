-- Prove2me | Theorems.Thm_GlobalTheory_Nef_PolesOfT_val_aeval_le
-- name    : GlobalTheory.Nef.PolesOfT.val_aeval_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:32.792206+00:00
-- url     : https://prove2.me/theorems/c9d52a41-972c-4274-8c10-2c7f7ade07dd
-- title:
--   Poles Of T: val aeval le
-- statement:
--   The Poles Of T construction uses the val aeval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsManyBoundedByPow.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsManyBoundedByPow.lean#L21-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsManyBoundedByPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PolesOfT
open Polynomial
variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem GlobalTheory.Nef.PolesOfT.val_aeval_le (t : F) (p : k[X]) (v : Place k F) :
    v.1 (aeval t p) ≤ Mx t v ^ p.natDegree := by sorry
