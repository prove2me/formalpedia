-- Prove2me | Theorems.Thm_GlobalTheory_LeastExponentCompare_conj_iff
-- name    : GlobalTheory.LeastExponentCompare.conj_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:01:23.989801+00:00
-- url     : https://prove2.me/theorems/0d90932f-1e39-487c-9aee-a368210abd55
-- title:
--   Least Exponent Compare: conj iff
-- statement:
--   The Least Exponent Compare construction uses the conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPositiveAdd.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPositiveAdd.lean#L67-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_BalancedHermitianSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPositiveAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LeastExponentCompare
open NumberField NumberField.IsCMField TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
set_option autoImplicit false
open NumberField NumberField.IsCMField TensorProduct

theorem GlobalTheory.LeastExponentCompare.conj_iff (E : Type) [Field E] [NumberField E]
    (cj : E → E) :
    ((∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ ∃ z : E, cj z ≠ z) ↔
      ∃ _ : IsCMField E, cj = fun z => complexConj E z := by sorry
