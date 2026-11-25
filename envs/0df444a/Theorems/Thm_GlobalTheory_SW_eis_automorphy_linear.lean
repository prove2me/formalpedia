-- Prove2me | Theorems.Thm_GlobalTheory_SW_eis_automorphy_linear
-- name    : GlobalTheory.SW.eis_automorphy_linear
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:15:01.427503+00:00
-- url     : https://prove2.me/theorems/61133773-6f3b-4586-9c7d-9db803f8c7b9
-- title:
--   SW: eis automorphy linear
-- statement:
--   The SW construction uses the eis automorphy linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisAutomorphyLinear.lean#L143-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisAutomorphyLinear.lean#L143-L183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.EisTrans

theorem GlobalTheory.SW.eis_automorphy_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → ∀ Z ∈ Hn Ψ N, (∀ z z', Summable fun U : Lag E N => ‖eisTerm Ψ U.2.choose φ Z z z'‖) ∧ (∀ γ ∈ UU E N, eis Ψ (weil Ψ γ φ) (hAct Ψ γ Z) 0 0 = hFac Ψ γ Z (0 : CM Ψ n N) 0 * eis Ψ φ Z 0 0) ∧ (∀ ψ, IsSB ψ → ∀ z z', eis Ψ (φ + ψ) Z z z' = eis Ψ φ Z z z' + eis Ψ ψ Z z z') ∧ ∀ (c : ℂ) z z', eis Ψ (c • φ) Z z z' = c * eis Ψ φ Z z z' := by sorry
