-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_lead_minor
-- name    : GlobalTheory.MinorGerm.lead_minor
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:42.739349+00:00
-- url     : https://prove2.me/theorems/e03144cd-337e-4120-a3ec-29118b3207d4
-- title:
--   Minor Germ: lead minor
-- statement:
--   The Minor Germ construction uses the lead minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L304-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L304-L330

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

theorem GlobalTheory.MinorGerm.lead_minor (j : Fin N × Fin N' → σ) (hj : ∀ b c, p (j (b, c)) ↔ b.val = c.val) {k : ℕ}
    (hk : k ≤ min N N') :
    Lead p (∑ ρ ∈ Finset.range k, dgOne j ρ 1) (MvPolynomial.rename j (minorK C N N' k)) := by sorry
