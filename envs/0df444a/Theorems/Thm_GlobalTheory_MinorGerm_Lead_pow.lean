-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_Lead_pow
-- name    : GlobalTheory.MinorGerm.Lead.pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:31.142449+00:00
-- url     : https://prove2.me/theorems/80facbdb-63ff-4983-b7fa-a2c4c9ea52c6
-- title:
--   Lead: pow
-- statement:
--   The Lead construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L165-L172

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

theorem GlobalTheory.MinorGerm.Lead.pow {α : σ →₀ ℕ} {P : MvPolynomial σ C} (hP : Lead p α P) (n : ℕ) :
    Lead p (n • α) (P ^ n) := by sorry
