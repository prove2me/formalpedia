-- Prove2me | Theorems.Thm_GlobalTheory_Tw_theta_props
-- name    : GlobalTheory.Tw.theta_props
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:13:45.012878+00:00
-- url     : https://prove2.me/theorems/9fbe1903-3f73-4772-bee4-ae675fd18ceb
-- title:
--   Tw: theta props
-- statement:
--   The Tw construction uses the theta props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L112-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryTwistInvolutionGLProperties.lean#L112-L132

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix
open GlobalTheory.Tw.PhiConjugateTranspose

theorem GlobalTheory.Tw.theta_props : ∀ (n : ℕ) (R : Type) [CommRing R] [StarRing R], (Phi n R * (Phi n R)ᵀ = 1) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit (theta g) ∧ theta (theta g) = g) ∧ (∀ g h : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit h → theta (g * h) = theta g * theta h) ∧ (∀ x δ : Matrix (Fin n) (Fin n) R, IsUnit x → IsUnit δ → nrm (twConj x δ) = x⁻¹ * nrm δ * x) ∧ (∀ u δ : Matrix (Fin n) (Fin n) R, IsUnit u → IsUnit δ → nrm (δ * theta u) = nrm δ * ((theta δ)⁻¹ * theta u * theta δ) * u) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → g.BlockTriangular id → (theta g).BlockTriangular id) ∧ ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → (theta g).det * star g.det = 1 := by sorry
