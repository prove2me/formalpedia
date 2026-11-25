-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_Lead_mul
-- name    : GlobalTheory.MinorGerm.Lead.mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:29.717216+00:00
-- url     : https://prove2.me/theorems/4cac4880-3aaf-4f14-b12b-9b34f07abd74
-- title:
--   Lead: mul
-- statement:
--   The Lead construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L142-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L142-L154

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
variable {p : σ → Prop} [DecidablePred p]

theorem GlobalTheory.MinorGerm.Lead.mul {α β : σ →₀ ℕ} {P Q : MvPolynomial σ C} (hP : Lead p α P) (hQ : Lead p β Q) :
    Lead p (α + β) (P * Q) := by sorry
