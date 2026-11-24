-- Prove2me | Theorems.Thm_GlobalTheory_PairingInvariants_eval_act_of_mul_eq_one
-- name    : GlobalTheory.PairingInvariants.eval_act_of_mul_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:55.641834+00:00
-- url     : https://prove2.me/theorems/4b975b57-9d6c-4d4d-958d-319240f2f097
-- title:
--   Pairing Invariants: eval act of mul eq one
-- statement:
--   The Pairing Invariants construction uses the eval act of mul eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L118-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L118-L138

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

theorem GlobalTheory.PairingInvariants.eval_act_of_mul_eq_one (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ z, MvPolynomial.eval (act u (fun t => (u t).map conj) z) p = MvPolynomial.eval z p)
    (g h : T → Matrix (Fin n) (Fin n) ℂ) (hgh : ∀ t, g t * (h t)ᵀ = 1)
    (z : T × Bool × Fin n × Fin N → ℂ) :
    MvPolynomial.eval (act g h z) p = MvPolynomial.eval z p := by sorry
