-- Prove2me | Theorems.Thm_GlobalTheory_NoetherPrimitive_exists_map_eq_C_mul
-- name    : GlobalTheory.NoetherPrimitive.exists_map_eq_C_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:07:58.697195+00:00
-- url     : https://prove2.me/theorems/c40386d5-e8fd-41de-aebe-3eb3dc494782
-- title:
--   Noether Primitive: exists map eq C mul
-- statement:
--   The Noether Primitive construction uses the exists map eq C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsPrimitiveElementDiscriminantMultiple.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsPrimitiveElementDiscriminantMultiple.lean#L13-L18

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

theorem GlobalTheory.NoetherPrimitive.exists_map_eq_C_mul {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (f : K[X]) :
    ∃ s : R, s ≠ 0 ∧ ∃ g : R[X], g.map (algebraMap R K) = C (algebraMap R K s) * f := by sorry
