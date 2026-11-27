-- Prove2me | Theorems.Thm_GroundTheory_LocalField_quasiChar_apply_eq_of_isUnramified
-- name    : GroundTheory.LocalField.quasiChar_apply_eq_of_isUnramified
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:01.696144+00:00
-- url     : https://prove2.me/theorems/e59005b1-b376-58b0-aa33-f5a518cffcd9
-- title:
--   Local Field: quasi Char apply eq of is Unramified
-- statement:
--   The Local Field construction uses the quasi Char apply eq of is Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaChar.lean#L64-L66

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

theorem GroundTheory.LocalField.quasiChar_apply_eq_of_isUnramified (h : IsUnramifiedChar χ) {π : Kˣ}
    (hπ : ord (π : K) = 1) : χ π = χ (unifUnit K) := by sorry
