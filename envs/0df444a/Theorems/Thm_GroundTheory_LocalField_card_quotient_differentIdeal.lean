-- Prove2me | Theorems.Thm_GroundTheory_LocalField_card_quotient_differentIdeal
-- name    : GroundTheory.LocalField.card_quotient_differentIdeal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:30.284113+00:00
-- url     : https://prove2.me/theorems/bdde6306-9bf4-5899-b806-2fc0d86507af
-- title:
--   Local Field: card quotient different Ideal
-- statement:
--   The Local Field construction uses the card quotient different Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem GroundTheory.LocalField.card_quotient_differentIdeal :
    Nat.card (𝒪[L] ⧸ differentIdeal 𝒪[K] 𝒪[L]) = residueCard L ^ differentExponent K L := by sorry
