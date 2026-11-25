-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_low_monG
-- name    : GlobalTheory.MinorGerm.low_monG
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:10.045744+00:00
-- url     : https://prove2.me/theorems/2603f16e-72f3-4a07-9463-4a55f2ed4d62
-- title:
--   Minor Germ: low mon G
-- statement:
--   The Minor Germ construction uses the low mon G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L344-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L344-L356

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
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}
variable {p : σ → Prop} [DecidablePred p]

theorem GlobalTheory.MinorGerm.low_monG (j : Fin N × Fin N' → σ) {t : σ → MvPowerSeries σ C} (ht : TangentId t)
    (e : ℕ → ℕ) : Low (dg j (monAl N N' e)) (monG N N' e fun x => t (j x)) := by sorry
