-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Converse_isSquare_completion
-- name    : GlobalTheory.QuadSymbol.Converse.isSquare_completion
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:54.67815+00:00
-- url     : https://prove2.me/theorems/c65c8227-9ad3-4733-8cec-54c59547311b
-- title:
--   Converse: is Square completion
-- statement:
--   The Converse construction uses the is Square completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEverywhereNormDivOfEtaProdEqOne.lean#L127-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEverywhereNormDivOfEtaProdEqOne.lean#L127-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEverywhereNormDivOfEtaProdEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.HilbertRecip
open GlobalTheory.QuadSymbol.Converse
variable {K : Type} [Field K]

theorem GlobalTheory.QuadSymbol.Converse.isSquare_completion {σ : K →+* ℝ} {δ : K} (h : IsSquare (σ δ)) :
    IsSquare (algebraMap K (realPlace σ).Completion δ) := by sorry
