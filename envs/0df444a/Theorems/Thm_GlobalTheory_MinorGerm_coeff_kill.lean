-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_coeff_kill
-- name    : GlobalTheory.MinorGerm.coeff_kill
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:41.966795+00:00
-- url     : https://prove2.me/theorems/9abe53a1-8bd6-4d72-b4ec-b8cd1da262bc
-- title:
--   Minor Germ: coeff kill
-- statement:
--   The Minor Germ construction uses the coeff kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L107-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L107-L131

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

theorem GlobalTheory.MinorGerm.coeff_kill (p : σ → Prop) [DecidablePred p] (m : σ →₀ ℕ) (hm : ∀ x ∈ m.support, p x)
    (P : MvPolynomial σ C) : MvPolynomial.coeff m (kill p P) = MvPolynomial.coeff m P := by sorry
