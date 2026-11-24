-- Prove2me | Theorems.Thm_GlobalTheory_PairingInvariants_eval_act_diagonal
-- name    : GlobalTheory.PairingInvariants.eval_act_diagonal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:00.411356+00:00
-- url     : https://prove2.me/theorems/6db9b42e-90f4-4fe7-9f0c-15226ff59e25
-- title:
--   Pairing Invariants: eval act diagonal
-- statement:
--   The Pairing Invariants construction uses the eval act diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L79-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L79-L116

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

theorem GlobalTheory.PairingInvariants.eval_act_diagonal (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ z, MvPolynomial.eval (act u (fun t => (u t).map conj) z) p = MvPolynomial.eval z p)
    (a : T → Fin n → ℝ) (z : T × Bool × Fin n × Fin N → ℂ) :
    MvPolynomial.eval (act (fun t => diagonal fun i => cexp (a t i))
      (fun t => diagonal fun i => cexp (-(a t i : ℂ))) z) p = MvPolynomial.eval z p := by sorry
