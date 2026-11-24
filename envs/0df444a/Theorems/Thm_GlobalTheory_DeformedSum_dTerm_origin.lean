-- Prove2me | Theorems.Thm_GlobalTheory_DeformedSum_dTerm_origin
-- name    : GlobalTheory.DeformedSum.dTerm_origin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:36:27.686355+00:00
-- url     : https://prove2.me/theorems/e6bf5bcc-c333-4b85-a581-e9e0357fc8ee
-- title:
--   Deformed Sum: d Term origin
-- statement:
--   The Deformed Sum construction uses the d Term origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DTermOrigin.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DTermOrigin.lean#L20-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_DefiningCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates
open GlobalTheory GlobalTheory.DeformedSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem GlobalTheory.DeformedSum.dTerm_origin (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E) :
    dTerm φ k m 0 x = risingFactor k m * ∏ i, ((φ i x)⁻¹ ^ (k + m i) * (starRingEnd ℂ (φ i x)) ^ m i) := by sorry
