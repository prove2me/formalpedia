-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_exists_chain
-- name    : GlobalTheory.CompanionTheory.Kloc.Fresnel.exists_chain
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:50:21.178663+00:00
-- url     : https://prove2.me/theorems/9503543a-efa8-47f4-91cc-31a687600ad3
-- title:
--   Fresnel: exists chain
-- statement:
--   The Fresnel construction uses the exists chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L296-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean#L296-L321

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem GlobalTheory.CompanionTheory.Kloc.Fresnel.exists_chain (C : ℂ) (k a : ℝ) (hC : C ≠ 0) (hk : k ≠ 0) (ha : a = 2 * |k|)
    (R : V ≃ₗᵢ[ℝ] V) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : 𝓢(V, ℂ),
      kerOp C a R (kerOp C a R (kerOp C a R (fun u => chirp k u *
        kerOp C a R (fun u => chirp k u * φ u) u))) 0 = c * ∫ v, φ v := by sorry
