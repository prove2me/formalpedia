-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ordRat_eq_ordRat_iff
-- name    : GroundTheory.LocalField.ordRat_eq_ordRat_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:14.140787+00:00
-- url     : https://prove2.me/theorems/f7348ab7-7f25-4643-965e-7c7e33cf58a3
-- title:
--   Local Field: ord Rat eq ord Rat iff
-- statement:
--   The Local Field construction uses the ord Rat eq ord Rat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/SeparableClosureValuation.lean#L271-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/SeparableClosureValuation.lean#L271-L274

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
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
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [Algebra K Ω] [ValuativeExtension K Ω]
variable {K}
variable [Algebra.IsAlgebraic K Ω]

theorem GroundTheory.LocalField.ordRat_eq_ordRat_iff {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordRat K x = ordRat K y ↔ valuation Ω x = valuation Ω y := by sorry
