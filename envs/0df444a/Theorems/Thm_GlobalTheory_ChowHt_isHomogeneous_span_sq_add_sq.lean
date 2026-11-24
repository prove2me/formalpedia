-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_isHomogeneous_span_sq_add_sq
-- name    : GlobalTheory.ChowHt.isHomogeneous_span_sq_add_sq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:40.8775+00:00
-- url     : https://prove2.me/theorems/fe227f7c-1d97-4cbd-8a41-f592de84ad4f
-- title:
--   Chow Ht: is Homogeneous span sq add sq
-- statement:
--   The Chow Ht construction uses the is Homogeneous span sq add sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L330-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L330-L335

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

theorem GlobalTheory.ChowHt.isHomogeneous_span_sq_add_sq :
    (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}).IsHomogeneous
      (homogeneousSubmodule (Fin 2) ℚ) := by sorry
