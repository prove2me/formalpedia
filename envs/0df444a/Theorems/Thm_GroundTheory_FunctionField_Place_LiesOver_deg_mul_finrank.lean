-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_deg_mul_finrank
-- name    : GroundTheory.FunctionField.Place.LiesOver.deg_mul_finrank
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:16.711894+00:00
-- url     : https://prove2.me/theorems/3bf0a827-3779-47c0-acb5-3a36cf6e0d8e
-- title:
--   Lies Over: deg mul finrank
-- statement:
--   The Lies Over construction uses the deg mul finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L213-L220

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
variable [IsFunctionField k K]
variable [IsFunctionField k K']
omit [IsFunctionField k K']

theorem GroundTheory.FunctionField.Place.LiesOver.deg_mul_finrank {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    letI := h.isLocalHom
    v.deg * Module.finrank v.ResidueField w.ResidueField = w.deg := by sorry
