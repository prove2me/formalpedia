-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_quot_levi
-- name    : GlobalTheory.Doubling.quot_levi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:45.508024+00:00
-- url     : https://prove2.me/theorems/85329202-f451-4975-b276-aca3b9d50479
-- title:
--   Doubling: quot levi
-- statement:
--   The Doubling construction uses the quot levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L287-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L287-L300

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι)
variable [Fintype n] [Fintype ι]
variable {e}
variable [DecidableEq n] [DecidableEq ι]
variable (e)

theorem GlobalTheory.Doubling.quot_levi {σ : A →+* A} {J : Matrix n n A} {M : Matrix ι ι A} (hM : cT σ M * dblGram e J * M = dblGram e J)
    (h : KeepsDiag e M) : cT σ (quotMat e M) * J * leviMat e M = J := by sorry
