-- Prove2me | Theorems.Thm_GlobalTheory_JacobiDeriv_norm_term_eq
-- name    : GlobalTheory.JacobiDeriv.norm_term_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:18.314703+00:00
-- url     : https://prove2.me/theorems/8a4bf13f-5d9d-4f16-b573-956fe0b4b114
-- title:
--   Jacobi Deriv: norm term eq
-- statement:
--   The Jacobi Deriv construction uses the norm term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DifferentiableAtDerivAtZero.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DifferentiableAtDerivAtZero.lean#L53-L61

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

theorem GlobalTheory.JacobiDeriv.norm_term_eq (n : ℤ) (τ : ℂ) :
    ‖jacobiTheta₂'_term n ((τ + 1) / 2) τ‖ =
      2 * π * |(n : ℝ)| * Real.exp (-(π * (n * (n + 1)) * τ.im)) := by sorry
