-- Prove2me | Theorems.Thm_GlobalTheory_SW_UnitaryLeft_mul_of_mulVec
-- name    : GlobalTheory.SW.UnitaryLeft.mul_of_mulVec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:41.120129+00:00
-- url     : https://prove2.me/theorems/51d22822-92aa-41d9-8a3a-55bf69c5f462
-- title:
--   Unitary Left: mul of mul Vec
-- statement:
--   The Unitary Left construction uses the mul of mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L96-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UnitaryLeft
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem GlobalTheory.SW.UnitaryLeft.mul_of_mulVec (P : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : Matrix (Fin n) (Fin N) ℂ) :
    P * (Matrix.of fun k => A *ᵥ z k) = Matrix.of fun k => A *ᵥ (P * z) k := by sorry
