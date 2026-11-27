-- Prove2me | Theorems.Thm_GlobalTheory_isDiscreteValuationRing_and_finite_residueField_of_numberField
-- name    : GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:06.057873+00:00
-- url     : https://prove2.me/theorems/252cbd96-2ae9-5d4b-87ae-15428bf73c37
-- title:
--   Global Theory: is Discrete Valuation Ring and finite residue Field of number Field
-- statement:
--   The Global Theory construction uses the is Discrete Valuation Ring and finite residue Field of number Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDiscreteValuationRingAndFiniteResidueFieldValu.lean#L57-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsDiscreteValuationRingAndFiniteResidueFieldValu.lean#L57-L113

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

theorem GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField {L : Type*} [Field L]
    [NumberField L] (W : ValuationSubring L) {n : ℕ} (hn : n ≠ (0 : ℕ))
    (hW : (↑n : L) ∈ W.nonunits) :
      IsDiscreteValuationRing ↥W ∧ Finite (IsLocalRing.ResidueField ↥W) := by sorry
