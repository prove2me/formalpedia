-- Prove2me | Theorems.Thm_GlobalTheory_SW_swd_tendsto_zero_at_cusps
-- name    : GlobalTheory.SW.swd_tendsto_zero_at_cusps
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:34.693135+00:00
-- url     : https://prove2.me/theorems/5482b1c0-cf62-4bb4-aed9-9adc1c95507d
-- title:
--   SW: swd tendsto zero at cusps
-- statement:
--   The SW construction uses the swd tendsto zero at cusps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SwdTendstoZeroAtCusps.lean#L163-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SwdTendstoZeroAtCusps.lean#L163-L181

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilActionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelOperatorHermitianEisensteinSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SwdTendstoZeroAtCusps
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
open GlobalTheory.SW.Cusp

theorem GlobalTheory.SW.swd_tendsto_zero_at_cusps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∀ v : Fin (N + 1) → E, v ≠ 0 → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by sorry
