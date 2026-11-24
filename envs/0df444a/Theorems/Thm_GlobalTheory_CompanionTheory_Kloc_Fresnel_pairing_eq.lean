-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_pairing_eq
-- name    : GlobalTheory.CompanionTheory.Kloc.Fresnel.pairing_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:01.671457+00:00
-- url     : https://prove2.me/theorems/c737d289-e029-4ad4-a78b-d87f8fb5e705
-- title:
--   Fresnel: pairing eq
-- statement:
--   The Fresnel construction uses the pairing eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L357-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L357-L368

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {m n : ℕ}

theorem GlobalTheory.CompanionTheory.Kloc.Fresnel.pairing_eq (s : ℂ) (hs : s ≠ 0) (hω : ‖s / ‖s‖‖ = 1) (u v : Fin m → Fin n → ℂ) :
    (s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re =
      ‖s‖ * inner ℝ (matEquiv m n u) (unitMul _ (s / ‖s‖) hω (matEquiv m n v)) := by sorry
