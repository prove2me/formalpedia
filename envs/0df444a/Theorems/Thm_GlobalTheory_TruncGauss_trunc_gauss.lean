-- Prove2me | Theorems.Thm_GlobalTheory_TruncGauss_trunc_gauss
-- name    : GlobalTheory.TruncGauss.trunc_gauss
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:53.968985+00:00
-- url     : https://prove2.me/theorems/d56af4fb-a39c-43a2-8fbe-06865c72aa8e
-- title:
--   Trunc Gauss: trunc gauss
-- statement:
--   The Trunc Gauss construction uses the trunc gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L151-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L151-L212

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.TruncGauss

theorem GlobalTheory.TruncGauss.trunc_gauss : ∀ (n : ℕ) (C ε : ℝ), 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ →
    ∀ᶠ m : ℕ in atTop, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.PosSemidef → (∀ j l, ‖H j l‖ ≤ C) →
      1 ≤ (H.det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ,
        Real.exp (-(m * ((∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) := by sorry
