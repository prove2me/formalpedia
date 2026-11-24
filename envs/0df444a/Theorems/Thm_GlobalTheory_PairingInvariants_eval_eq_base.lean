-- Prove2me | Theorems.Thm_GlobalTheory_PairingInvariants_eval_eq_base
-- name    : GlobalTheory.PairingInvariants.eval_eq_base
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:13.746532+00:00
-- url     : https://prove2.me/theorems/5a57a416-8db6-41bc-82b1-e7a1715003ca
-- title:
--   Pairing Invariants: eval eq base
-- statement:
--   The Pairing Invariants construction uses the eval eq base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L203-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L203-L237

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

theorem GlobalTheory.PairingInvariants.eval_eq_base [Finite T] (hN : N ≤ n) (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ g h : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, g t * (h t)ᵀ = 1) →
      ∀ z, MvPolynomial.eval (act g h z) p = MvPolynomial.eval z p)
    (z : T × Bool × Fin n × Fin N → ℂ) :
    MvPolynomial.eval z p = MvPolynomial.eval (base z) p := by sorry
