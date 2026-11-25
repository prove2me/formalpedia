-- Prove2me | Theorems.Thm_GlobalTheory_Nef_RatDilation_coe_comp_C_mul_X
-- name    : GlobalTheory.Nef.RatDilation.coe_comp_C_mul_X
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:53.340594+00:00
-- url     : https://prove2.me/theorems/ffe28a89-6107-47b5-b2df-583ed284b96d
-- title:
--   Rat Dilation: coe comp C mul X
-- statement:
--   The Rat Dilation construction uses the coe comp C mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatDegreeEqZeroOfSqDvd.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatDegreeEqZeroOfSqDvd.lean#L13-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeEqZeroOfSqDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open Polynomial
open GlobalTheory.Nef.RatDilation

theorem GlobalTheory.Nef.RatDilation.coe_comp_C_mul_X {F : Type} [Field F] (a : F) (f : F[X]) :
    ((f.comp (C a * X) : F[X]) : PowerSeries F) = PowerSeries.rescale a (f : PowerSeries F) := by sorry
