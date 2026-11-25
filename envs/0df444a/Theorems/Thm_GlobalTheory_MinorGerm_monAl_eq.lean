-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_monAl_eq
-- name    : GlobalTheory.MinorGerm.monAl_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:44:43.458173+00:00
-- url     : https://prove2.me/theorems/eee9a62b-784e-4444-a814-9771da28bd59
-- title:
--   Minor Germ: mon Al eq
-- statement:
--   The Minor Germ construction uses the mon Al eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L254-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L254-L262

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

theorem GlobalTheory.MinorGerm.monAl_eq (e : ℕ → ℕ) (ρ : ℕ) :
    monAl N N' e ρ = ∑ k ∈ Finset.Icc 1 (min N N'), if ρ < k then e k else 0 := by sorry
