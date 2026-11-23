-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_mem_scaleLat
-- name    : GlobalTheory.HTLat.mem_scaleLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:13.923144+00:00
-- url     : https://prove2.me/theorems/ce479e92-05ab-42b5-9645-ddd052445b66
-- title:
--   HTLat: mem scale Lat
-- statement:
--   The HTLat construction uses the mem scale Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L159-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L159-L160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]

theorem GlobalTheory.HTLat.mem_scaleLat {a : C} {La : Submodule O U} {x : U} :
    x ∈ scaleLat a La ↔ ∃ y ∈ La, a • y = x := by sorry
