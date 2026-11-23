-- Prove2me | Theorems.Thm_GlobalTheory_PairingInvariants_eq_at_zero_of_countable
-- name    : GlobalTheory.PairingInvariants.eq_at_zero_of_countable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:41.82224+00:00
-- url     : https://prove2.me/theorems/c2034505-49e2-4c74-a27c-22c563c8c081
-- title:
--   Pairing Invariants: eq at zero of countable
-- statement:
--   The Pairing Invariants construction uses the eq at zero of countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L145-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L145-L147

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
variable {T : Type} {n N : ℕ}

theorem GlobalTheory.PairingInvariants.eq_at_zero_of_countable {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {S : Set ℂ} (hS : S.Countable) (h : ∀ c ∉ S, F c = G c) : F 0 = G 0 := by sorry
