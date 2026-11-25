-- Prove2me | Theorems.Thm_GlobalTheory_SW_UnitaryLeft_transH_mul
-- name    : GlobalTheory.SW.UnitaryLeft.transH_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:47:15.890279+00:00
-- url     : https://prove2.me/theorems/ae98e30b-7c15-4738-8519-cf6de03e8296
-- title:
--   Unitary Left: trans H mul
-- statement:
--   The Unitary Left construction uses the trans H mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L112-L120

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

theorem GlobalTheory.SW.UnitaryLeft.transH_mul {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (γ : M2 E N)
    {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (H : TransH Ψ γ φ ψ) :
    TransH Ψ γ (fun x : Matrix (Fin n) (Fin N) E => φ (h * x))
      (fun x : Matrix (Fin n) (Fin N) E => ψ (h * x)) := by sorry
