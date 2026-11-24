-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_LagDeriv_iteratedDeriv_zero_eq_lag
-- name    : GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:31.079426+00:00
-- url     : https://prove2.me/theorems/84bd6a3e-2def-4d3a-9bb0-f66aecfd3d7a
-- title:
--   Lag Deriv: iterated Deriv zero eq lag
-- statement:
--   The Lag Deriv construction uses the iterated Deriv zero eq lag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivZeroEqLaguerreDerivativePolynomialV.lean#L196-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedDerivZeroEqLaguerreDerivativePolynomialV.lean#L196-L202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivZeroEqLaguerreDerivativePolynomialV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.LagDeriv
set_option autoImplicit false
open Filter Topology

theorem GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag : ∀ (k n : ℕ) (c y : ℂ),
    iteratedDeriv n (fun z : ℂ ↦ (1 + z * c)⁻¹ ^ k * Complex.exp (y * z / (1 + z * c))) 0 =
      _root_.GlobalTheory.HilbFam.lag k n c y := by sorry
