-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisTrans_entry_bound
-- name    : GlobalTheory.SW.EisTrans.entry_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:35:31.185083+00:00
-- url     : https://prove2.me/theorems/b7aee7bd-24da-4e7e-b00a-0231a46423dc
-- title:
--   Eis Trans: entry bound
-- statement:
--   The Eis Trans construction uses the entry bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisAutomorphyLinear.lean#L41-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EisAutomorphyLinear.lean#L41-L80

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisTrans
variable {N : ℕ}

theorem GlobalTheory.SW.EisTrans.entry_bound {C D Z : Matrix (Fin N) (Fin N) ℂ} {δ : ℝ} (hδ : 0 < δ)
    (h : D * Cᴴ = C * Dᴴ) (hQ : (C * Z + D).det ≠ 0)
    (hZ : (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) (i j : Fin N) :
    ‖((C * Z + D)⁻¹ * C) i j‖ ≤ δ⁻¹ := by sorry
