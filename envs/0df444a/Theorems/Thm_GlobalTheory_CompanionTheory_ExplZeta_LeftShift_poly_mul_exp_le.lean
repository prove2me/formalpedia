-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_poly_mul_exp_le
-- name    : GlobalTheory.CompanionTheory.ExplZeta.LeftShift.poly_mul_exp_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:37:56.729611+00:00
-- url     : https://prove2.me/theorems/c962e414-e6ae-4bec-8e17-c256a38f2118
-- title:
--   Left Shift: poly mul exp le
-- statement:
--   The Left Shift construction uses the poly mul exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L17-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L17-L36

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IntegralLeftVerticalLineBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplZeta GlobalTheory.CompanionTheory.ExplZeta.LeftShift

theorem GlobalTheory.CompanionTheory.ExplZeta.LeftShift.poly_mul_exp_le {σ : ℝ} (hσ : σ ≤ 0) :
    (2 + |σ|) * Real.exp (σ / 2) ≤ 4 * Real.exp (σ / 4) := by sorry
