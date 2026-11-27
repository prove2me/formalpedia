-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_exists_sum_basis_tmul
-- name    : GlobalTheory.RegSS.exists_sum_basis_tmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T06:20:59.462802+00:00
-- url     : https://prove2.me/theorems/925004c7-c40c-4e62-9bca-c78beaf667f6
-- title:
--   Reg SS: exists sum basis tmul
-- statement:
--   The Reg SS construction uses the exists sum basis tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L64-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorCommutant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS

theorem GlobalTheory.RegSS.exists_sum_basis_tmul {F P A : Type} [Field F] [AddCommGroup P] [Module F P]
    [AddCommGroup A] [Module F A] {n : Type} [Fintype n] (b : Module.Basis n F P)
    (x : P ⊗[F] A) : ∃ a : n → A, ∑ j, b j ⊗ₜ[F] a j = x := by sorry
