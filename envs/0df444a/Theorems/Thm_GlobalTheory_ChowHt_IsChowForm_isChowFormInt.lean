-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_IsChowForm_isChowFormInt
-- name    : GlobalTheory.ChowHt.IsChowForm.isChowFormInt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:09:30.836522+00:00
-- url     : https://prove2.me/theorems/ffe2ccd2-c1f0-4c37-aa13-374ad642384a
-- title:
--   Is Chow Form: is Chow Form Int
-- statement:
--   The Is Chow Form construction uses the is Chow Form Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L59-L62

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

theorem GlobalTheory.ChowHt.IsChowForm.isChowFormInt {I : Ideal (MvPolynomial (Fin N) k)} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (h : IsChowForm I e dl f) :
    IsChowFormInt I e dl f := by sorry
