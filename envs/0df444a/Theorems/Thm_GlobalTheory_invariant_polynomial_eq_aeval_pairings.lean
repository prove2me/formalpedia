-- Prove2me | Theorems.Thm_GlobalTheory_invariant_polynomial_eq_aeval_pairings
-- name    : GlobalTheory.invariant_polynomial_eq_aeval_pairings
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:16.544505+00:00
-- url     : https://prove2.me/theorems/505ecc4e-df50-4b1a-84c4-6d16b8ae1203
-- title:
--   Global Theory: invariant polynomial eq aeval pairings
-- statement:
--   The Global Theory construction uses the invariant polynomial eq aeval pairings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L243-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean#L243-L259

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
open GlobalTheory.PairingInvariants

theorem GlobalTheory.invariant_polynomial_eq_aeval_pairings :
    ∀ (T : Type) [Fintype T] [DecidableEq T] (n N : ℕ), N ≤ n → ∀ p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ, (∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ z : T × Bool × Fin n × Fin N → ℂ, MvPolynomial.eval (fun v => ∑ l, (if v.2.1 then u v.1 v.2.2.1 l else conj (u v.1 v.2.2.1 l)) * z (v.1, v.2.1, l, v.2.2.2)) p = MvPolynomial.eval z p) → ∃ s : MvPolynomial (T × Fin N × Fin N) ℂ, p = MvPolynomial.aeval (fun v : T × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)) s := by sorry
