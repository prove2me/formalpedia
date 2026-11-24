-- Prove2me | Theorems.Thm_GlobalTheory_isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime
-- name    : GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:57.747772+00:00
-- url     : https://prove2.me/theorems/9987d857-ce25-4371-aea1-ffdd779f15fa
-- title:
--   Global Theory: is Discrete Valuation Ring and finite residue Field valuation Subring At Prime
-- statement:
--   The Global Theory construction uses the is Discrete Valuation Ring and finite residue Field valuation Subring At Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDiscreteValuationRingAndFiniteResidueFieldValu.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDiscreteValuationRingAndFiniteResidueFieldValu.lean#L10-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing NumberField IsDedekindDomain
open GlobalTheory
open IsLocalRing IsDedekindDomain NumberField

theorem GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime
    {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R)
    (hfin : Finite (R ⧸ v.asIdeal)) :
      IsDiscreteValuationRing ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) ∧
        Finite (IsLocalRing.ResidueField
          ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)) := by sorry
