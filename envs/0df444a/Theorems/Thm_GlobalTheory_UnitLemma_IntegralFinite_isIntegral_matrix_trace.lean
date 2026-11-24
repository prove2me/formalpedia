-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_IntegralFinite_isIntegral_matrix_trace
-- name    : GlobalTheory.UnitLemma.IntegralFinite.isIntegral_matrix_trace
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:51.782688+00:00
-- url     : https://prove2.me/theorems/22e1b4b4-d22a-4748-a9d4-d53f5c32ba36
-- title:
--   Integral Finite: is Integral matrix trace
-- statement:
--   The Integral Finite construction uses the is Integral matrix trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteIntegralClosureOfSeparableInvolutionAlgebr.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteIntegralClosureOfSeparableInvolutionAlgebr.lean#L15-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteIntegralClosureOfSeparableInvolutionAlgebr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.IntegralFinite
open Matrix

theorem GlobalTheory.UnitLemma.IntegralFinite.isIntegral_matrix_trace {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) : IsIntegral R M.trace := by sorry
