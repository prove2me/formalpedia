-- Prove2me | Theorems.Thm_GlobalTheory_T_polyDeriv_aeval_pairings_eq_zero_of_isHeat
-- name    : GlobalTheory.T.polyDeriv_aeval_pairings_eq_zero_of_isHeat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:38:08.487456+00:00
-- url     : https://prove2.me/theorems/4b985686-529c-4f4d-b07e-c6b2a34996c2
-- title:
--   T: poly Deriv aeval pairings eq zero of is Heat
-- statement:
--   The T construction uses the poly Deriv aeval pairings eq zero of is Heat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PolyDerivPairingEqZeroOfIsHeatStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PolyDerivPairingEqZeroOfIsHeatStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PolyDerivPairingEqZeroOfIsHeat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PolyDerivPairingEqZeroOfIsHeatStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.polyDeriv_aeval_pairings_eq_zero_of_isHeat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ), IsHeat Ψ D → (∀ Z ∈ Hn Ψ N, D Z 0 0 = 0) → ∀ Z ∈ Hn Ψ N, ∀ s : MvPolynomial (Ψ × Fin N × Fin N) ℂ, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) s) (fun v => (Pi.single v 1 : Ψ × Bool × Fin n × Fin N → ℂ)) (fun w : Ψ × Bool × Fin n × Fin N → ℂ => D Z (fun τ => Matrix.of fun k a => w (τ, false, k, a)) (fun τ => Matrix.of fun k a => w (τ, true, k, a))) 0 = 0 := by sorry
