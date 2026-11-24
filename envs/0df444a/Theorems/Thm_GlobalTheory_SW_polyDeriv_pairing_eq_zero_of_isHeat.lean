-- Prove2me | Theorems.Thm_GlobalTheory_SW_polyDeriv_pairing_eq_zero_of_isHeat
-- name    : GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:49:14.707505+00:00
-- url     : https://prove2.me/theorems/15190bd5-9fc6-468f-a316-49fdc638a77d
-- title:
--   SW: poly Deriv pairing eq zero of is Heat
-- statement:
--   The SW construction uses the poly Deriv pairing eq zero of is Heat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PolyDerivPairingEqZeroOfIsHeat.lean#L167-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PolyDerivPairingEqZeroOfIsHeat.lean#L167-L290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PolyDerivPairingEqZeroOfIsHeat
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
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical

theorem GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (D : _root_.GlobalTheory.SW.CM Ψ N N → _root_.GlobalTheory.SW.CM Ψ n N → _root_.GlobalTheory.SW.CM Ψ n N → ℂ), _root_.GlobalTheory.SW.IsHeat Ψ D → (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, D Z 0 0 = 0) → ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ s : MvPolynomial (Ψ × Fin N × Fin N) ℂ, _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) s) (fun v => (Pi.single v 1 : Ψ × Bool × Fin n × Fin N → ℂ)) (fun w : Ψ × Bool × Fin n × Fin N → ℂ => D Z (fun τ => Matrix.of fun k a => w (τ, false, k, a)) (fun τ => Matrix.of fun k a => w (τ, true, k, a))) 0 = 0 := by sorry
