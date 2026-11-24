-- Prove2me | Theorems.Thm_GlobalTheory_T_unramifiedInvolutionExt_maps_integers_to_integers
-- name    : GlobalTheory.T.unramifiedInvolutionExt_maps_integers_to_integers
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:01:01.118585+00:00
-- url     : https://prove2.me/theorems/0396a470-0b1c-4609-b50e-f4b58d2c4431
-- title:
--   T: unramified Involution Ext maps integers to integers
-- statement:
--   The T construction uses the unramified Involution Ext maps integers to integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedInvolutionExtMapsIntegersToIntegersStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedInvolutionExtMapsIntegersToIntegersStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedInvolutionExtMapsIntegersToIntegers
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedInvolutionExtMapsIntegersToIntegersStatement
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

theorem GlobalTheory.T.unramifiedInvolutionExt_maps_integers_to_integers : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ x : K.O, ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by sorry
