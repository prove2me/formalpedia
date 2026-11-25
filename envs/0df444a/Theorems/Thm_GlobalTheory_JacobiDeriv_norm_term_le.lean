-- Prove2me | Theorems.Thm_GlobalTheory_JacobiDeriv_norm_term_le
-- name    : GlobalTheory.JacobiDeriv.norm_term_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:28.780097+00:00
-- url     : https://prove2.me/theorems/fbfb7c40-9348-5268-9211-370f9159eff9
-- title:
--   Jacobi Deriv: norm term le
-- statement:
--   The Jacobi Deriv construction uses the norm term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DifferentiableAtDerivAtZero.lean#L63-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DifferentiableAtDerivAtZero.lean#L63-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DifferentiableAtDerivAtZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real
open GlobalTheory GlobalTheory.JacobiDeriv

theorem GlobalTheory.JacobiDeriv.norm_term_le {T : ℝ} (hT : 0 < T) (n : ℤ) {τ : ℂ} (hτ : T ≤ τ.im) :
    ‖jacobiTheta₂'_term n ((τ + 1) / 2) τ‖ ≤
      2 * π * (|(n : ℝ)| ^ 1 * Real.exp (-π * (T * n ^ 2 - 2 * (T / 2) * |(n : ℝ)|))) := by sorry
