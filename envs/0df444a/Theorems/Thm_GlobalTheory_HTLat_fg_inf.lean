-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_fg_inf
-- name    : GlobalTheory.HTLat.fg_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:15.69581+00:00
-- url     : https://prove2.me/theorems/3655f684-88f4-4d7a-b444-2760876bcd2e
-- title:
--   HTLat: fg inf
-- statement:
--   The HTLat construction uses the fg inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L227-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L227-L270

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
variable (v : Valuation C ℝ≥0)
variable {v}
set_option autoImplicit false
open scoped TensorProduct NNReal NumberField Pointwise
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]
variable (v : Valuation C ℝ≥0)
variable {v}

theorem GlobalTheory.HTLat.fg_inf (hv : v.Integers O) {La : Submodule O U} (hfg : La.FG)
    (F : Submodule C U) : (La ⊓ F.restrictScalars O).FG := by sorry
