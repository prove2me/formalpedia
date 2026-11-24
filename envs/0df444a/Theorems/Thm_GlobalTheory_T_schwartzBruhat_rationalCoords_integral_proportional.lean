-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartzBruhat_rationalCoords_integral_proportional
-- name    : GlobalTheory.T.schwartzBruhat_rationalCoords_integral_proportional
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:57:34.360789+00:00
-- url     : https://prove2.me/theorems/372adb0d-4603-4255-8df2-bdcb766a9968
-- title:
--   T: schwartz Bruhat rational Coords integral proportional
-- statement:
--   The T construction uses the schwartz Bruhat rational Coords integral proportional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatRationalCoordsIntegralProportionalStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatRationalCoordsIntegralProportionalStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportionalStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartzBruhat_rationalCoords_integral_proportional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → haar (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) = c * haar φ := by sorry
