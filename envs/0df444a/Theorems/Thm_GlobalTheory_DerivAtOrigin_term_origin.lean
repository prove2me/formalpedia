-- Prove2me | Theorems.Thm_GlobalTheory_DerivAtOrigin_term_origin
-- name    : GlobalTheory.DerivAtOrigin.term_origin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:52.822081+00:00
-- url     : https://prove2.me/theorems/98c4158e-aa35-4e72-be64-ca8e3c2d68a0
-- title:
--   Deriv At Origin: term origin
-- statement:
--   The Deriv At Origin construction uses the term origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivFormulaOfSeries.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivFormulaOfSeries.lean#L35-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivFormulaOfSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DerivAtOrigin

theorem GlobalTheory.DerivAtOrigin.term_origin {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (x : E) :
    term φ k κ 0 x = ∏ i, ((φ i x)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i x)) ^ κ i) := by sorry
