-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_finrank_residueField
-- name    : GroundTheory.FunctionField.Place.LiesOver.finrank_residueField
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:37.393955+00:00
-- url     : https://prove2.me/theorems/82ada536-b57c-423a-88b9-ecff71e9e35f
-- title:
--   Lies Over: finrank residue Field
-- statement:
--   The Lies Over construction uses the finrank residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L224-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean#L224-L230

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

theorem GroundTheory.FunctionField.Place.LiesOver.finrank_residueField {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    letI := h.isLocalHom
    Module.finrank v.ResidueField w.ResidueField = w.inertiaDeg v := by sorry
