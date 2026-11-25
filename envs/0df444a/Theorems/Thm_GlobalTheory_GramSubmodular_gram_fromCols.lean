-- Prove2me | Theorems.Thm_GlobalTheory_GramSubmodular_gram_fromCols
-- name    : GlobalTheory.GramSubmodular.gram_fromCols
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:03.34137+00:00
-- url     : https://prove2.me/theorems/4a28ca7e-8226-4181-b6fe-46422eed4af4
-- title:
--   Gram Submodular: gram from Cols
-- statement:
--   The Gram Submodular construction uses the gram from Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetFromColsEqZero.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetFromColsEqZero.lean#L17-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetFromColsEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open GlobalTheory.GramSubmodular
variable {m α β γ : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem GlobalTheory.GramSubmodular.gram_fromCols (U : Matrix m α ℂ) (V : Matrix m β ℂ) :
    (fromCols U V)ᴴ * fromCols U V = fromBlocks (Uᴴ * U) (Uᴴ * V) (Vᴴ * U) (Vᴴ * V) := by sorry
