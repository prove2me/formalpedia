-- Prove2me | Theorems.Thm_GlobalTheory_LeastExponentCompare_isCMField_of_conj
-- name    : GlobalTheory.LeastExponentCompare.isCMField_of_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:01:17.224815+00:00
-- url     : https://prove2.me/theorems/6a3239e8-8ee8-4dcb-b5ca-9fe7a2fa7c93
-- title:
--   Least Exponent Compare: is CMField of conj
-- statement:
--   The Least Exponent Compare construction uses the is CMField of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPositiveAdd.lean#L12-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPositiveAdd.lean#L12-L62

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

theorem GlobalTheory.LeastExponentCompare.isCMField_of_conj (E : Type) [Field E] [NumberField E] (cj : E → E)
    (h : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) (hne : ∃ z : E, cj z ≠ z) :
    IsCMField E := by sorry
