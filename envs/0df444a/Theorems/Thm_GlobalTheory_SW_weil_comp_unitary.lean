-- Prove2me | Theorems.Thm_GlobalTheory_SW_weil_comp_unitary
-- name    : GlobalTheory.SW.weil_comp_unitary
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:50.874798+00:00
-- url     : https://prove2.me/theorems/1138d419-4822-487f-9764-c5f001eb5136
-- title:
--   SW: weil comp unitary
-- statement:
--   The SW construction uses the weil comp unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L128-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L128-L151

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
open GlobalTheory.SW.UnitaryLeft

theorem GlobalTheory.SW.weil_comp_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (fun x : Matrix (Fin n) (Fin N) E => φ (h * x)) ∧ (∀ γ ∈ UU E N, weil Ψ γ (fun x => φ (h * x)) = fun x => weil Ψ γ φ (h * x)) ∧ ∀ Z ∈ Hn Ψ N, thH Ψ (fun x => φ (h * x)) Z 0 0 = thH Ψ φ Z 0 0 ∧ eis Ψ (fun x => φ (h * x)) Z 0 0 = eis Ψ φ Z 0 0 := by sorry
