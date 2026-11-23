-- Prove2me | Theorems.Thm_GlobalTheory_PairingInvariants_act_diagonal
-- name    : GlobalTheory.PairingInvariants.act_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:34.033608+00:00
-- url     : https://prove2.me/theorems/1e837d51-b0a3-4f37-a2d1-144ae66034bc
-- title:
--   Pairing Invariants: act diagonal
-- statement:
--   The Pairing Invariants construction uses the act diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L65-L69

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

theorem GlobalTheory.PairingInvariants.act_diagonal (a b : T → Fin n → ℂ) (z : T × Bool × Fin n × Fin N → ℂ) :
    act (fun t => diagonal (a t)) (fun t => diagonal (b t)) z =
      fun v => (if v.2.1 then a v.1 v.2.2.1 else b v.1 v.2.2.1) * z v := by sorry
