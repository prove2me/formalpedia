-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isUnramifiedChar_iff
-- name    : GroundTheory.LocalField.isUnramifiedChar_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:55.551921+00:00
-- url     : https://prove2.me/theorems/e086f9c7-b89a-4e2f-80fc-155d0bf7b30c
-- title:
--   Local Field: is Unramified Char iff
-- statement:
--   The Local Field construction uses the is Unramified Char iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L55-L57

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (χ : Kˣ →* ℂˣ)
variable {χ}

theorem GroundTheory.LocalField.isUnramifiedChar_iff : IsUnramifiedChar χ ↔ ∀ u : Kˣ, ord (u : K) = 0 → χ u = 1 := by sorry
