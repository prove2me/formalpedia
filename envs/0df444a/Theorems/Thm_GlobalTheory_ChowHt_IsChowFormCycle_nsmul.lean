-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_IsChowFormCycle_nsmul
-- name    : GlobalTheory.ChowHt.IsChowFormCycle.nsmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:49.550584+00:00
-- url     : https://prove2.me/theorems/6cf14152-78ab-439c-a6c2-c466903e071f
-- title:
--   Is Chow Form Cycle: nsmul
-- statement:
--   The Is Chow Form Cycle construction uses the nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L289-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L289-L296

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

theorem GlobalTheory.ChowHt.IsChowFormCycle.nsmul {Z : Ideal (MvPolynomial (Fin N) k) →₀ ℕ} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (h : IsChowFormCycle Z e dl f) (m : ℕ) :
    IsChowFormCycle (m • Z) e (m * dl) (f ^ m) := by sorry
