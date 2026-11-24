-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KWhit_norm_det_bottom_block_sq
-- name    : GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:18.13054+00:00
-- url     : https://prove2.me/theorems/cd17fa3b-454d-4d85-bc27-ccee69903f0f
-- title:
--   KWhit: norm det bottom block sq
-- statement:
--   The KWhit construction uses the norm det bottom block sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DetSqNormEqHermitianBlockFormula.lean#L7-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DetSqNormEqHermitianBlockFormula.lean#L7-L120

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetSqNormEqHermitianBlockFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KWhit

theorem GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq :
    ∀ {n : Type} [Fintype n] [DecidableEq n] (t u D K₁ K₂ β h g : Matrix n n ℂ) (e η : ℂ),
      ‖e‖ = 1 → η ≠ 0 → K₁ * K₁ᴴ + K₂ * K₂ᴴ = 1 → e • t = D * K₁ → e • (β * u) = D * K₂ →
      tᴴ * u = 1 → hᴴ = h → β = -(η • hᵀ) →
      g * uᴴ = ((‖η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 → IsUnit g.det →
      ‖D.det‖ ^ 2 = ‖t.det‖ ^ 2 *
        (1 + (g⁻¹ * h.map star * g⁻¹ᴴ) * (g⁻¹ * h.map star * g⁻¹ᴴ)).det.re := by sorry
