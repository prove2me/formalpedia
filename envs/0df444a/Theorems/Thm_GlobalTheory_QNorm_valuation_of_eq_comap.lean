-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_valuation_of_eq_comap
-- name    : GlobalTheory.QNorm.valuation_of_eq_comap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:22.090009+00:00
-- url     : https://prove2.me/theorems/025ba7a9-e9ee-48f6-b5df-5625151486f4
-- title:
--   QNorm: valuation of eq comap
-- statement:
--   The QNorm construction uses the valuation of eq comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/WithZeroEqOfLeExpIff.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/WithZeroEqOfLeExpIff.lean#L62-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero

theorem GlobalTheory.QNorm.valuation_of_eq_comap {E : Type} [Field E] [NumberField E] (σ : E ≃+* E)
    (w w' : HeightOneSpectrum (𝓞 E))
    (h : w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ)) (y : E) :
    w'.valuation E y = w.valuation E (σ y) := by sorry
