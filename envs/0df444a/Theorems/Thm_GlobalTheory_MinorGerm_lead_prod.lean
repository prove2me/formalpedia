-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_lead_prod
-- name    : GlobalTheory.MinorGerm.lead_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:44.322791+00:00
-- url     : https://prove2.me/theorems/192fde67-01f9-479d-b21a-f638bacaad2d
-- title:
--   Minor Germ: lead prod
-- statement:
--   The Minor Germ construction uses the lead prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L156-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L156-L163

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

theorem GlobalTheory.MinorGerm.lead_prod {ι : Type} (s : Finset ι) (α : ι → σ →₀ ℕ) (P : ι → MvPolynomial σ C)
    (h : ∀ i ∈ s, Lead p (α i) (P i)) : Lead p (∑ i ∈ s, α i) (∏ i ∈ s, P i) := by sorry
