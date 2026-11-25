-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_adjoin_inv_eq
-- name    : GroundTheory.FunctionField.Place.adjoin_inv_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:04.912409+00:00
-- url     : https://prove2.me/theorems/ca3083f5-c8b3-4528-a219-775348fce81b
-- title:
--   Place: adjoin inv eq
-- statement:
--   The Place construction uses the adjoin inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBridge.lean#L337-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBridge.lean#L337-L343

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
open scoped IntermediateField.algebraAdjoinAdjoin
variable [IsFunctionField k K] (t : K) [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K]
attribute [local instance] isDedekindDomain_closure_adjoin isFractionRing_closure_adjoin
omit [IsFunctionField k K] [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K]

theorem GroundTheory.FunctionField.Place.adjoin_inv_eq : IntermediateField.adjoin k {t⁻¹} = IntermediateField.adjoin k {t} := by sorry
