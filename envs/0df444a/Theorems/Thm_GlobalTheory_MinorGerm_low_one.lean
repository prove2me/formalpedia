-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_low_one
-- name    : GlobalTheory.MinorGerm.low_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:29.113826+00:00
-- url     : https://prove2.me/theorems/d3083abe-e514-4e5a-9eff-9c0cfdde91d3
-- title:
--   Minor Germ: low one
-- statement:
--   The Minor Germ construction uses the low one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L17-L20

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

theorem GlobalTheory.MinorGerm.low_one : Low (0 : σ →₀ ℕ) (1 : MvPowerSeries σ C) := by sorry
