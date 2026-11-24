-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_intMap_isIntegral_of_unr
-- name    : GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:57.04698+00:00
-- url     : https://prove2.me/theorems/e65fab39-52f3-4cb0-80c4-9430038dd063
-- title:
--   Unr: int Map is Integral of unr
-- statement:
--   The Unr construction uses the int Map is Integral of unr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegerMapIsIntegralUnramifiedInvolutionEx.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegerMapIsIntegralUnramifiedInvolutionEx.lean#L11-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerMapIsIntegralUnramifiedInvolutionEx
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

theorem GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧
      @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := by sorry
