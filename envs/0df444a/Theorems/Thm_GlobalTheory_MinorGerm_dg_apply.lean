-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_dg_apply
-- name    : GlobalTheory.MinorGerm.dg_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:04.542662+00:00
-- url     : https://prove2.me/theorems/b9debd4d-2e8e-4019-8ac6-fcf8093834a5
-- title:
--   Minor Germ: dg apply
-- statement:
--   The Minor Germ construction uses the dg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L358-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L358-L383

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

theorem GlobalTheory.MinorGerm.dg_apply (j : Fin N × Fin N' → σ) (hj : Function.Injective j) (f : ℕ → ℕ)
    (b : Fin N) (c : Fin N') : dg j f (j (b, c)) = if b.val = c.val then f b.val else 0 := by sorry
