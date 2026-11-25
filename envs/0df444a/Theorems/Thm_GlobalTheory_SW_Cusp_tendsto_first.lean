-- Prove2me | Theorems.Thm_GlobalTheory_SW_Cusp_tendsto_first
-- name    : GlobalTheory.SW.Cusp.tendsto_first
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:45:12.267461+00:00
-- url     : https://prove2.me/theorems/363c823f-8816-43c7-9050-bd98f0d6bf0c
-- title:
--   Cusp: tendsto first
-- statement:
--   The Cusp construction uses the tendsto first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SwdTendstoZeroAtCusps.lean#L144-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SwdTendstoZeroAtCusps.lean#L144-L157

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Cusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

theorem GlobalTheory.SW.Cusp.tendsto_first {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (hn : Even n)
    (hN : 4 * (N + 1) < n) (hsw : SWAt Ψ n N) {M R : ℕ} {φ : Fam E n (N + 1)} (hφ : admitted M R φ)
    {Z : CM Ψ (N + 1) (N + 1)} (hZ : Z ∈ Hn Ψ (N + 1)) :
    Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 0) := by sorry
