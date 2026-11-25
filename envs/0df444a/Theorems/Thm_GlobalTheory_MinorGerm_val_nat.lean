-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_val_nat
-- name    : GlobalTheory.MinorGerm.val_nat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:44:28.837321+00:00
-- url     : https://prove2.me/theorems/cd0fd05d-a62c-4cd3-9984-d5963c8ba17b
-- title:
--   Minor Germ: val nat
-- statement:
--   The Minor Germ construction uses the val nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L462-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L462-L473

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

theorem GlobalTheory.MinorGerm.val_nat {l : ℕ} (hl : l.Prime) (hv : v (l : C) = 1) {n : ℕ} (hn : n ≠ 0) :
    v (n : C) = (((padicValNat l n : ℕ) : ℝ) : WithTop ℝ) := by sorry
