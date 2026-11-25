-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_exists_generator
-- name    : GlobalTheory.HTLat.exists_generator
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:38.146832+00:00
-- url     : https://prove2.me/theorems/434e45fe-b2da-4fe3-9dce-6d3dd2c731d5
-- title:
--   HTLat: exists generator
-- statement:
--   The HTLat construction uses the exists generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L190-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L190-L218

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

theorem GlobalTheory.HTLat.exists_generator (hv : v.Integers O) {La : Submodule O U} (hfg : La.FG) {x : U}
    (h₁ : La ≤ (Submodule.span C {x}).restrictScalars O) (h₂ : La ≠ ⊥) :
    ∃ c : C, c ≠ 0 ∧ La = Submodule.span O {c • x} := by sorry
