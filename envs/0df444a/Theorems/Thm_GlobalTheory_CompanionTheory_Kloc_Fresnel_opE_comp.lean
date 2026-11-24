-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_opE_comp
-- name    : GlobalTheory.CompanionTheory.Kloc.Fresnel.opE_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:50:51.585864+00:00
-- url     : https://prove2.me/theorems/c08b97bc-34b3-4713-94ff-92974b23329a
-- title:
--   Fresnel: op E comp
-- statement:
--   The Fresnel construction uses the op E comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L398-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L398-L408

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

theorem GlobalTheory.CompanionTheory.Kloc.Fresnel.opE_comp (C s : ℂ) (hs : s ≠ 0) (hω : ‖s / ‖s‖‖ = 1) (κ : ℝ)
    (hκ : ∀ F : EuclideanSpace ℂ (Fin m × Fin n) → ℂ,
      ∫ u : Fin m → Fin n → ℂ, F (matEquiv m n u) = κ * ∫ y, F y)
    (g : EuclideanSpace ℂ (Fin m × Fin n) → ℂ) :
    opE C s (g ∘ matEquiv m n) =
      kerOp (C * κ) ‖s‖ (unitMul _ (s / ‖s‖) hω) g ∘ matEquiv m n := by sorry
