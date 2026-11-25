-- Prove2me | Theorems.Thm_GlobalTheory_BasePointFree_HC_add_smul_left
-- name    : GlobalTheory.BasePointFree.HC_add_smul_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:35.456355+00:00
-- url     : https://prove2.me/theorems/4bf1af69-2560-48c2-99be-e49c176d7940
-- title:
--   Base Point Free: HC add smul left
-- statement:
--   The Base Point Free construction uses the HC add smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNeZeroPair.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNeZeroPair.lean#L27-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.BasePointFree

theorem GlobalTheory.BasePointFree.HC_add_smul_left {ι : Type} [Fintype ι] {n : ℕ} (w c γ : Fin n → EuclideanSpace ℂ ι)
    (a : ℂ) : HC (w + a • c) γ = HC w γ + a * HC c γ := by sorry
