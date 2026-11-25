-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_Low_pow
-- name    : GlobalTheory.MinorGerm.Low.pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:44:30.886772+00:00
-- url     : https://prove2.me/theorems/d1b30b3f-4b2b-46f5-84b3-a1965f9bcd4f
-- title:
--   Low: pow
-- statement:
--   The Low construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L83-L90

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}

theorem GlobalTheory.MinorGerm.Low.pow {α : σ →₀ ℕ} {g : MvPowerSeries σ C} (hg : Low α g) (n : ℕ) :
    Low (n • α) (g ^ n) := by sorry
