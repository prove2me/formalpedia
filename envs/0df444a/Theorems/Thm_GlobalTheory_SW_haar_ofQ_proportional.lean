-- Prove2me | Theorems.Thm_GlobalTheory_SW_haar_ofQ_proportional
-- name    : GlobalTheory.SW.haar_ofQ_proportional
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:17.697748+00:00
-- url     : https://prove2.me/theorems/95913c8d-802d-4b31-b2c5-bc0db6ce619c
-- title:
--   SW: haar of Q proportional
-- statement:
--   The SW construction uses the haar of Q proportional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatRationalCoordsIntegralProportional.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatRationalCoordsIntegralProportional.lean#L113-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportional
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

theorem GlobalTheory.SW.haar_ofQ_proportional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → haar (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) = c * haar φ := by sorry
