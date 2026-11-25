-- Prove2me | Theorems.Thm_GlobalTheory_SW_Cusp_pushZ_mem
-- name    : GlobalTheory.SW.Cusp.pushZ_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:51:17.614738+00:00
-- url     : https://prove2.me/theorems/a505f60e-d4b7-5cd4-83d7-5f2c55f9afa5
-- title:
--   Cusp: push Z mem
-- statement:
--   The Cusp construction uses the push Z mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SwdTendstoZeroAtCusps.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SwdTendstoZeroAtCusps.lean#L54-L65

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
import Theorems.Thm_GlobalTheory_SW_EisSiegel_pushZ_mem
import Theorems.Thm_GlobalTheory_SW_SiegelOp_pushZ_mem

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
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.Cusp.pushZ_mem (Ψ : Finset (E →+* ℂ)) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ}
    (ht : 0 ≤ t) : pushZ Ψ Z v t ∈ Hn Ψ N := by sorry
