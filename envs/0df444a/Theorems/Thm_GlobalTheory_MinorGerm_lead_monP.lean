-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_lead_monP
-- name    : GlobalTheory.MinorGerm.lead_monP
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:11.545473+00:00
-- url     : https://prove2.me/theorems/78d9e876-cddb-4986-bbeb-41db6227d63c
-- title:
--   Minor Germ: lead mon P
-- statement:
--   The Minor Germ construction uses the lead mon P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L332-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L332-L342

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

theorem GlobalTheory.MinorGerm.lead_monP (j : Fin N × Fin N' → σ) (hj : ∀ b c, p (j (b, c)) ↔ b.val = c.val)
    (e : ℕ → ℕ) :
    Lead p (dg j (monAl N N' e)) (MvPolynomial.rename j (monP C N N' e)) := by sorry
