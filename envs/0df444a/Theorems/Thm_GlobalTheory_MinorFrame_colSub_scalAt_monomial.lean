-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_colSub_scalAt_monomial
-- name    : GlobalTheory.MinorFrame.colSub_scalAt_monomial
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:04:59.819656+00:00
-- url     : https://prove2.me/theorems/cf107332-5fbf-449a-9ada-bf4f8b0396d5
-- title:
--   Minor Frame: col Sub scal At monomial
-- statement:
--   The Minor Frame construction uses the col Sub scal At monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralDetCharacterFockColumnSubstitutionEqZero.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralDetCharacterFockColumnSubstitutionEqZero.lean#L28-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.colSub_scalAt_monomial {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (t : Var ι d a →₀ ℕ) (c : ℂ) :
    colSub (scalAt τ₀ ζ) (monomial t c : Pol ι d a) = monomial t (c * ζ ^ degAt τ₀ t) := by sorry
