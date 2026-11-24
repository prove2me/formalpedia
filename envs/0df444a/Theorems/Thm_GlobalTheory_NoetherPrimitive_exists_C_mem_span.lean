-- Prove2me | Theorems.Thm_GlobalTheory_NoetherPrimitive_exists_C_mem_span
-- name    : GlobalTheory.NoetherPrimitive.exists_C_mem_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:40.811009+00:00
-- url     : https://prove2.me/theorems/9efc3bef-1c7b-4493-93c0-293732572169
-- title:
--   Noether Primitive: exists C mem span
-- statement:
--   The Noether Primitive construction uses the exists C mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsPrimitiveElementDiscriminantMultiple.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsPrimitiveElementDiscriminantMultiple.lean#L20-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsPrimitiveElementDiscriminantMultiple
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

theorem GlobalTheory.NoetherPrimitive.exists_C_mem_span {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (p : R[X]) (hp : (p.map (algebraMap R K)).Separable) :
    ∃ q : R, q ≠ 0 ∧ C q ∈ Ideal.span {p, p.derivative} := by sorry
