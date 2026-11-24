-- Prove2me | Theorems.Thm_GlobalTheory_CMType_sum_univ_eq
-- name    : GlobalTheory.CMType.sum_univ_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:04:02.622457+00:00
-- url     : https://prove2.me/theorems/089b3fec-1848-4f01-92cf-aa4ca257c0e0
-- title:
--   CMType: sum univ eq
-- statement:
--   The CMType construction uses the sum univ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean#L88-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.CMType
variable {E : Type*} [Field E] [NumberField E] (Φ : CMType E)

theorem GlobalTheory.CMType.sum_univ_eq {M : Type*} [AddCommMonoid M] (g : (E →+* ℂ) → M) :
    ∑ τ, g τ = ∑ τ : Φ, (g τ + g (ComplexEmbedding.conjugate τ.1)) := by sorry
