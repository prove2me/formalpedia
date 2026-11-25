-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isUnramifiedChar_inv_iff
-- name    : GroundTheory.LocalField.isUnramifiedChar_inv_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:16:37.527157+00:00
-- url     : https://prove2.me/theorems/81dcbb5b-e4f6-5317-9ccd-ef43ae599ebc
-- title:
--   Local Field: is Unramified Char inv iff
-- statement:
--   The Local Field construction uses the is Unramified Char inv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L50-L51

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
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
variable {χ : Kˣ →* ℂˣ}

theorem GroundTheory.LocalField.isUnramifiedChar_inv_iff : IsUnramifiedChar χ⁻¹ ↔ IsUnramifiedChar χ := by sorry
