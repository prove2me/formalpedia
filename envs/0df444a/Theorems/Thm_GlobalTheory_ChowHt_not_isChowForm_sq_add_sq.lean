-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_not_isChowForm_sq_add_sq
-- name    : GlobalTheory.ChowHt.not_isChowForm_sq_add_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:13.975921+00:00
-- url     : https://prove2.me/theorems/831bdd02-657a-471f-8ace-d25bdb52a986
-- title:
--   Chow Ht: not is Chow Form sq add sq
-- statement:
--   The Chow Ht construction uses the not is Chow Form sq add sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L381-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L381-L394

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

theorem GlobalTheory.ChowHt.not_isChowForm_sq_add_sq (δ : ℕ) (f : MvPolynomial (Fin (0 + 1) × Fin 2) ℚ) :
    ¬ IsChowForm (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)}) 0 δ f := by sorry
