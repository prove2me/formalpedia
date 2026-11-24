-- Prove2me | Theorems.Thm_GlobalTheory_CapelliTop_qdet_expand
-- name    : GlobalTheory.CapelliTop.qdet_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:13.700869+00:00
-- url     : https://prove2.me/theorems/bd409824-39f2-4393-8f30-72e229bc4231
-- title:
--   Capelli Top: qdet expand
-- statement:
--   The Capelli Top construction uses the qdet expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QdetTopThreeOrders.lean#L49-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QdetTopThreeOrders.lean#L49-L72

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CapelliTop
variable {A : Type} [Ring A] {n : ℕ}

theorem GlobalTheory.CapelliTop.qdet_expand [Algebra ℂ A] (E : Fin n → Fin n → A) (u : ℂ) :
    Formalism.REAL.qdet E u = ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, (u - (k : ℂ))) • subdet E S := by sorry
