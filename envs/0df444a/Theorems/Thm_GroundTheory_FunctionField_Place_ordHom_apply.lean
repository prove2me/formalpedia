-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- name    : GroundTheory.FunctionField.Place.ordHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:00.918947+00:00
-- url     : https://prove2.me/theorems/2085797e-383d-4c0d-ad85-30b40bcf3ebb
-- title:
--   Place: ord Hom apply
-- statement:
--   The Place construction uses the ord Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L481-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean#L481-L482

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IntermediateField
open scoped WithZero
open Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
open GroundTheory.FunctionField.Place
variable {k K} (v : Place k K)
variable [IsFunctionField k K]

theorem GroundTheory.FunctionField.Place.ordHom_apply (x : Kˣ) : v.ordHom x = Multiplicative.ofAdd (v.ord x) := by sorry

attribute [defeq] GroundTheory.FunctionField.Place.ordHom_apply
