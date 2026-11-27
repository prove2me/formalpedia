-- Prove2me | Theorems.Thm_GlobalTheory_TwIntegral_integral_twConj_mem_cent_mul
-- name    : GlobalTheory.TwIntegral.integral_twConj_mem_cent_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:41.614509+00:00
-- url     : https://prove2.me/theorems/d0925e06-e37a-5ced-a5ba-cd52958598e0
-- title:
--   Tw Integral: integral tw Conj mem cent mul
-- statement:
--   The Tw Integral construction uses the integral tw Conj mem cent mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralTwConjMemCentMul.lean#L248-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralTwConjMemCentMul.lean#L248-L321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommutantMulIntegralConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitDiscriminantMatrixQuotientIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralTwConjMemCentMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix
open GlobalTheory GlobalTheory.TwIntegral
open Matrix

theorem GlobalTheory.TwIntegral.integral_twConj_mem_cent_mul : ∀ (F E : Type) [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [_root_.GlobalTheory.JR.Unram F E] (n : ℕ) (δ x : Matrix (Fin n) (Fin n) E),
    (∀ i j, ‖δ i j‖ ≤ 1) → ‖δ.det‖ = 1 →
    (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * (_root_.GlobalTheory.Tw.nrm δ).charpoly +
        v * Polynomial.derivative (_root_.GlobalTheory.Tw.nrm δ).charpoly = 1) →
    IsUnit x → (∀ i j, ‖_root_.GlobalTheory.Tw.twConj x δ i j‖ ≤ 1) →
    ‖(_root_.GlobalTheory.Tw.twConj x δ).det‖ = 1 →
    ∃ t ∈ _root_.GlobalTheory.Tw.cent δ, ∃ k : Matrix (Fin n) (Fin n) E, (∀ i j, ‖k i j‖ ≤ 1) ∧
      ‖k.det‖ = 1 ∧ x = t * k := by sorry
