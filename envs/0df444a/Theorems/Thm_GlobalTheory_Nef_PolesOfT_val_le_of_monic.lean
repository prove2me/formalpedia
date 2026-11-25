-- Prove2me | Theorems.Thm_GlobalTheory_Nef_PolesOfT_val_le_of_monic
-- name    : GlobalTheory.Nef.PolesOfT.val_le_of_monic
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:38.48581+00:00
-- url     : https://prove2.me/theorems/76d13a40-af40-4b30-b4ad-a4e8ac229dfa
-- title:
--   Poles Of T: val le of monic
-- statement:
--   The Poles Of T construction uses the val le of monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsManyBoundedByPow.lean#L36-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsManyBoundedByPow.lean#L36-L59

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

theorem GlobalTheory.Nef.PolesOfT.val_le_of_monic (t y : F) (P : F[X]) (hP : P.Monic) (hy : P.eval y = 0) (c : ℕ)
    (v : Place k F) (hc : ∀ i < P.natDegree, v.1 (P.coeff i) ≤ Mx t v ^ c) :
    v.1 y ≤ Mx t v ^ c := by sorry
