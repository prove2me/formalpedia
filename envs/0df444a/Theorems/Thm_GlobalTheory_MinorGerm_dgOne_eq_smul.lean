-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_dgOne_eq_smul
-- name    : GlobalTheory.MinorGerm.dgOne_eq_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:01.434337+00:00
-- url     : https://prove2.me/theorems/2f39aed5-7a95-4bc3-863c-74b86ac32495
-- title:
--   Minor Germ: dg One eq smul
-- statement:
--   The Minor Germ construction uses the dg One eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L244-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L244-L247

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

theorem GlobalTheory.MinorGerm.dgOne_eq_smul (j : Fin N × Fin N' → σ) (ρ n : ℕ) : dgOne j ρ n = n • dgOne j ρ 1 := by sorry
