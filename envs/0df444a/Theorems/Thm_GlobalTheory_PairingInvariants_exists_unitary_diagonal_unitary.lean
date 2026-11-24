-- Prove2me | Theorems.Thm_GlobalTheory_PairingInvariants_exists_unitary_diagonal_unitary
-- name    : GlobalTheory.PairingInvariants.exists_unitary_diagonal_unitary
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:29.594309+00:00
-- url     : https://prove2.me/theorems/59f4443d-b236-4eec-9947-5970d8966b98
-- title:
--   Pairing Invariants: exists unitary diagonal unitary
-- statement:
--   The Pairing Invariants construction uses the exists unitary diagonal unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L10-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L10-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.PairingInvariants

theorem GlobalTheory.PairingInvariants.exists_unitary_diagonal_unitary {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g) :
    ∃ (u₁ u₂ : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℝ), u₁ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      u₂ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      g = u₁ * diagonal (fun i => cexp (a i)) * u₂ := by sorry
