-- Prove2me | Theorems.Thm_GlobalTheory_SW_Vac_heisS_apply
-- name    : GlobalTheory.SW.Vac.heisS_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:23.722867+00:00
-- url     : https://prove2.me/theorems/05582df8-53b9-4406-b92a-06a7e3032386
-- title:
--   Vac: heis S apply
-- statement:
--   The Vac construction uses the heis S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L81-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.Vac.heisS_apply [DecidableEq ι] (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ) (x : Matrix κ ι ℚ) :
    heisS a b φ x = φ (x - b) * ex (2 * pr x a - pr a b) := by sorry
