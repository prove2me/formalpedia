-- Prove2me | Theorems.Thm_GlobalTheory_TruncGauss_trunc_lower
-- name    : GlobalTheory.TruncGauss.trunc_lower
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:19.772653+00:00
-- url     : https://prove2.me/theorems/967926cc-0b07-4eda-8ba6-54addc79c58a
-- title:
--   Trunc Gauss: trunc lower
-- statement:
--   The Trunc Gauss construction uses the trunc lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L82-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedGaussianIntegralUniformPosSemidef.lean#L82-L149

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

theorem GlobalTheory.TruncGauss.trunc_lower {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (η δ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (m : ℕ) (hm : 1 ≤ m) :
    Real.pi ^ n / (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re
        - Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n ≤
      (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ,
        Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2))) := by sorry
