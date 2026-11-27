-- Prove2me | Theorems.Thm_GlobalTheory_WModel_wModel_p_ne_zero
-- name    : GlobalTheory.WModel.wModel_p_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:42.432967+00:00
-- url     : https://prove2.me/theorems/4ec459c8-636a-541b-8b4b-6b61b85ae06a
-- title:
--   WModel: w Model p ne zero
-- statement:
--   The WModel construction uses the w Model p ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZmodPrimeSqLocal.lean#L272-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZmodPrimeSqLocal.lean#L272-L276

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_WFrobStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZmodPrimeSqLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2 TrivSqZeroExt
open GlobalTheory GlobalTheory.WModel
variable (p : ℕ) [hp : Fact p.Prime]

theorem GlobalTheory.WModel.wModel_p_ne_zero : (p : ((wModel p).W : Type)) ≠ 0 := by sorry
