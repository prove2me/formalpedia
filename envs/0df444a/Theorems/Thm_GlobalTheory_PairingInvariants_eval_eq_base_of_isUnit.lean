-- Prove2me | Theorems.Thm_GlobalTheory_PairingInvariants_eval_eq_base_of_isUnit
-- name    : GlobalTheory.PairingInvariants.eval_eq_base_of_isUnit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:21.799862+00:00
-- url     : https://prove2.me/theorems/5a052b4f-aef6-4816-b49a-d31fb5cede9a
-- title:
--   Pairing Invariants: eval eq base of is Unit
-- statement:
--   The Pairing Invariants construction uses the eval eq base of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L149-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L149-L201

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

theorem GlobalTheory.PairingInvariants.eval_eq_base_of_isUnit (hN : N ≤ n) (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ g h : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, g t * (h t)ᵀ = 1) →
      ∀ z, MvPolynomial.eval (act g h z) p = MvPolynomial.eval z p)
    (G : T → Matrix (Fin n) (Fin n) ℂ) (hG : ∀ t, IsUnit (G t))
    (z : T × Bool × Fin n × Fin N → ℂ) (hz : ∀ t k j, z (t, true, k, j) = G t k (Fin.castLE hN j)) :
    MvPolynomial.eval z p = MvPolynomial.eval (base z) p := by sorry
