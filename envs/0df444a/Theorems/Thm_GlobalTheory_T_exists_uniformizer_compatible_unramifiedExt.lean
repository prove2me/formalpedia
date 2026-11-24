-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_uniformizer_compatible_unramifiedExt
-- name    : GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:38:01.615474+00:00
-- url     : https://prove2.me/theorems/8c305cea-0f03-4754-8ab2-41fcdd8097b4
-- title:
--   T: exists uniformizer compatible unramified Ext
-- statement:
--   The T construction uses the exists uniformizer compatible unramified Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniformizerCompatibleUnramifiedExtStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniformizerCompatibleUnramifiedExtStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniformizerCompatibleUnramifiedExt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniformizerCompatibleUnramifiedExtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ π : K.O, ∃ π' : K'.O, algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) ∧ IsLocalRing.maximalIdeal K.O = Ideal.span {π} ∧ IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} := by sorry
