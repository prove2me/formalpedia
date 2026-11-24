-- Prove2me | Theorems.Thm_GlobalTheory_SW_Vac_intM_smul
-- name    : GlobalTheory.SW.Vac.intM_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:42:14.18096+00:00
-- url     : https://prove2.me/theorems/d618eb03-e018-465e-9de4-2eeddea4e0a6
-- title:
--   Vac: int M smul
-- statement:
--   The Vac construction uses the int M smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L125-L128

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
omit [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.Vac.intM_smul {x : Matrix κ ι ℚ} (n : ℕ) (h : IntM x) : IntM ((n : ℚ) • x) := by sorry
