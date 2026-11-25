-- Prove2me | Theorems.Thm_GlobalTheory_HTLat_exists_grAt_eq
-- name    : GlobalTheory.HTLat.exists_grAt_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:22.332888+00:00
-- url     : https://prove2.me/theorems/d12ebe06-e5e6-522e-ac00-35c06466e207
-- title:
--   HTLat: exists gr At eq
-- statement:
--   The HTLat construction uses the exists gr At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L343-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LogAbsVpOfNormalised.lean#L343-L444

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
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
set_option autoImplicit false
open scoped TensorProduct NNReal NumberField Pointwise
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}

theorem GlobalTheory.HTLat.exists_grAt_eq {v : Valuation C ℝ≥0} (hv : v.Integers O)
    {La : Submodule O U} (hfg : La.FG)
    (f : Fin N → U) (i : Fin N) (hf : f i ∉ _root_.GlobalTheory.HTLat.step C f i) {a : C}
    (ha : a ≠ 0) {y : U} (hy : y ∈ _root_.GlobalTheory.HTLat.step C f i)
    (hLa : a • f i + y ∈ La) :
    ∃ c : C, c ≠ 0 ∧ _root_.GlobalTheory.HTLat.grAt C La f i =
        Submodule.span O {c • (_root_.GlobalTheory.HTLat.step C f i).mkQ (f i)} ∧
      _root_.GlobalTheory.HTLat.grNorm v La f i = (v c)⁻¹ := by sorry
