-- Prove2me | Theorems.Thm_GlobalTheory_PairingInvariants_act_mul
-- name    : GlobalTheory.PairingInvariants.act_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:15.265451+00:00
-- url     : https://prove2.me/theorems/e96fa120-954d-4969-9314-0bad1203d279
-- title:
--   Pairing Invariants: act mul
-- statement:
--   The Pairing Invariants construction uses the act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L58-L63

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

theorem GlobalTheory.PairingInvariants.act_mul (g h g' h' : T → Matrix (Fin n) (Fin n) ℂ) (z : T × Bool × Fin n × Fin N → ℂ) :
    act (fun t => g t * g' t) (fun t => h t * h' t) z = act g h (act g' h' z) := by sorry
