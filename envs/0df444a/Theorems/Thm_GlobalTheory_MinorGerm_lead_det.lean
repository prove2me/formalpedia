-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_lead_det
-- name    : GlobalTheory.MinorGerm.lead_det
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:48:26.046345+00:00
-- url     : https://prove2.me/theorems/546c6573-18ec-4079-aacb-13ec022a2221
-- title:
--   Minor Germ: lead det
-- statement:
--   The Minor Germ construction uses the lead det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L193-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L193-L232

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

theorem GlobalTheory.MinorGerm.lead_det {k : ℕ} (w : Fin k → Fin k → σ) (hw : ∀ b c, p (w b c) ↔ b = c) :
    Lead p (∑ b, Finsupp.single (w b b) 1)
      (Matrix.of fun b c : Fin k => (MvPolynomial.X (w b c) : MvPolynomial σ C)).det := by sorry
