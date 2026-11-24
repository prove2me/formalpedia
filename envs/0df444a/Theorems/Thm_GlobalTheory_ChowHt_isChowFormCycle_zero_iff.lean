-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_isChowFormCycle_zero_iff
-- name    : GlobalTheory.ChowHt.isChowFormCycle_zero_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:30:19.462945+00:00
-- url     : https://prove2.me/theorems/5b5688f2-058f-4b4c-b640-254ecbce1237
-- title:
--   Chow Ht: is Chow Form Cycle zero iff
-- statement:
--   The Chow Ht construction uses the is Chow Form Cycle zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L281-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L281-L287

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

theorem GlobalTheory.ChowHt.isChowFormCycle_zero_iff {e dl : ℕ} {f : MvPolynomial (Fin (e + 1) × Fin N) k} :
    IsChowFormCycle 0 e dl f ↔ dl = 0 ∧ ∃ c : k, c ≠ 0 ∧ f = C c := by sorry
