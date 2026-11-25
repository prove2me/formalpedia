-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_val_coprime
-- name    : GlobalTheory.MinorGerm.val_coprime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:44:12.345291+00:00
-- url     : https://prove2.me/theorems/96585fa7-571e-4905-80d5-e011739333b6
-- title:
--   Minor Germ: val coprime
-- statement:
--   The Minor Germ construction uses the val coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L434-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L434-L460

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
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

theorem GlobalTheory.MinorGerm.val_coprime {l : ℕ} (hl : l.Prime) (hv : v (l : C) = 1) {n : ℕ} (hn : ¬ l ∣ n) :
    v (n : C) = 0 := by sorry
