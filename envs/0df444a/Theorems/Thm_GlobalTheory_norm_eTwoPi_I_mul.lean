-- Prove2me | Theorems.Thm_GlobalTheory_norm_eTwoPi_I_mul
-- name    : GlobalTheory.norm_eTwoPi_I_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:51.174989+00:00
-- url     : https://prove2.me/theorems/bd8e6367-c302-4b14-be05-5d678553f2aa
-- title:
--   Global Theory: norm e Two Pi I mul
-- statement:
--   The Global Theory construction uses the norm e Two Pi I mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentCoeffNegEqZeroOfBounded.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentCoeffNegEqZeroOfBounded.lean#L8-L11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentCoeffNegEqZeroOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
open GlobalTheory

theorem GlobalTheory.norm_eTwoPi_I_mul (y : ℝ) : ‖eTwoPi (Complex.I * y)‖ = Real.exp (-(2 * Real.pi * y)) := by sorry
