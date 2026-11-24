-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_gen_of_valuation_eq
-- name    : GlobalTheory.UnitLemma.Unr.exists_gen_of_valuation_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:35:36.842165+00:00
-- url     : https://prove2.me/theorems/144e87f9-1732-4610-9772-7dcfa127deca
-- title:
--   Unr: exists gen of valuation eq
-- statement:
--   The Unr construction uses the exists gen of valuation eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniformizerCompatibleUnramifiedExt.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniformizerCompatibleUnramifiedExt.lean#L11-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniformizerCompatibleUnramifiedExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.Unr.exists_gen_of_valuation_eq (K : UQ) (x : K.E)
    (hx : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x = WithZero.exp (-1)) :
    ∃ a : K.O, algebraMap K.O K.E a = x ∧ IsLocalRing.maximalIdeal K.O = Ideal.span {a} := by sorry
