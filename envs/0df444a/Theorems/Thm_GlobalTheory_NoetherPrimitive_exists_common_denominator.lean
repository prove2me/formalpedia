-- Prove2me | Theorems.Thm_GlobalTheory_NoetherPrimitive_exists_common_denominator
-- name    : GlobalTheory.NoetherPrimitive.exists_common_denominator
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:24.146152+00:00
-- url     : https://prove2.me/theorems/c5fc1ee8-d468-472c-83a6-9bfc6a5ec982
-- title:
--   Noether Primitive: exists common denominator
-- statement:
--   The Noether Primitive construction uses the exists common denominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsPrimitiveElementDiscriminantMultiple.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsPrimitiveElementDiscriminantMultiple.lean#L32-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsPrimitiveElementDiscriminantMultiple
import Theorems.Thm_GlobalTheory_CommonDenominatorForFinset_exists_common_denominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherPrimitive
open Polynomial
open scoped nonZeroDivisors

theorem GlobalTheory.NoetherPrimitive.exists_common_denominator {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Module.Finite R A] (a : A)
    (h : ∀ b : A, ∃ s : R, s ≠ 0 ∧ ∃ r : R[X], algebraMap R A s * b = aeval a r) :
    ∃ s : R, s ≠ 0 ∧ ∀ b : A, ∃ r : R[X], algebraMap R A s * b = aeval a r := by sorry
