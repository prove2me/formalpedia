-- Prove2me | Theorems.Thm_GlobalTheory_HCA_dw_continuousFunctional
-- name    : GlobalTheory.HCA.dw_continuousFunctional
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:59:02.143261+00:00
-- url     : https://prove2.me/theorems/8b898d21-48fb-4fe0-aedf-0b415118d575
-- title:
--   HCA: dw continuous Functional
-- statement:
--   The HCA construction uses the dw continuous Functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsContinuousFunctionalIterPartialDeriv.lean#L37-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsContinuousFunctionalIterPartialDeriv.lean#L37-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory Filter Topology
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.dw_continuousFunctional : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (B : Type)
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (R : B →ₗ[ℂ] (E d → ℂ)),
    (∀ x ∈ U, Continuous fun u => R u x) → (∀ u, ContDiffOn ℝ ∞ (R u) U) →
    ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : B →L[ℂ] ℂ, ∀ u, l u = dw w (R u) x := by sorry
