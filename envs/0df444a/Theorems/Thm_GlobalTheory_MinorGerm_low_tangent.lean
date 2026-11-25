-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_low_tangent
-- name    : GlobalTheory.MinorGerm.low_tangent
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:38.365791+00:00
-- url     : https://prove2.me/theorems/1531f5eb-bcc1-42ad-bc59-46eb7c22185f
-- title:
--   Minor Germ: low tangent
-- statement:
--   The Minor Germ construction uses the low tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L92-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L92-L102

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

theorem GlobalTheory.MinorGerm.low_tangent {t : σ → MvPowerSeries σ C} (ht : TangentId t) (x : σ) (n : ℕ) :
    Low (Finsupp.single x n) (t x ^ n) := by sorry
