-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_isChowFormCycle_two_sq_add_sq
-- name    : GlobalTheory.ChowHt.isChowFormCycle_two_sq_add_sq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:42.558804+00:00
-- url     : https://prove2.me/theorems/9f0f07ea-113e-58c5-82c3-a81f563ad0c0
-- title:
--   Chow Ht: is Chow Form Cycle two sq add sq
-- statement:
--   The Chow Ht construction uses the is Chow Form Cycle two sq add sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L396-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L396-L401

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}

theorem GlobalTheory.ChowHt.isChowFormCycle_two_sq_add_sq :
    IsChowFormCycle
      (Finsupp.single (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}) 2) 0 4
      ((X (0, 0) ^ 2 + X (0, 1) ^ 2) ^ 2) := by sorry
