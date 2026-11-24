-- Prove2me | Theorems.Thm_GlobalTheory_SW_Vac_exists_ex_of_pow
-- name    : GlobalTheory.SW.Vac.exists_ex_of_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:45:49.530133+00:00
-- url     : https://prove2.me/theorems/2cb923d6-6f98-420a-8d4c-b91fe250ffb7
-- title:
--   Vac: exists ex of pow
-- statement:
--   The Vac construction uses the exists ex of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L71-L79

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

theorem GlobalTheory.SW.Vac.exists_ex_of_pow {z : ℂ} {m : ℕ} (hm : 0 < m) (h : z ^ m = 1) :
    ∃ r : ℚ, z * ex (2 * r) = 1 := by sorry
