-- Prove2me | Theorems.Thm_GlobalTheory_SW_Vac_pr_smul_left
-- name    : GlobalTheory.SW.Vac.pr_smul_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:28.01992+00:00
-- url     : https://prove2.me/theorems/faddf4d7-70c8-438b-b438-b5dc33865466
-- title:
--   Vac: pr smul left
-- statement:
--   The Vac construction uses the pr smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L21-L22

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

theorem GlobalTheory.SW.Vac.pr_smul_left (c : ℚ) (x a : Matrix κ ι ℚ) : pr (c • x) a = c * pr x a := by sorry
