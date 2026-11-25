-- Prove2me | Theorems.Thm_GlobalTheory_lbIso_spreads_out
-- name    : GlobalTheory.lbIso_spreads_out
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:09:55.981983+00:00
-- url     : https://prove2.me/theorems/f7bd385e-dd0c-446a-adb4-83cbeadaa3e4
-- title:
--   Global Theory: lb Iso spreads out
-- statement:
--   The Global Theory construction uses the lb Iso spreads out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L473-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L473-L488

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory

theorem GlobalTheory.lbIso_spreads_out (k : IntermediateField ℚ ℂ) (B : Scheme.{0}) (pB : B ⟶ Sp k) [QuasiCompact pB]
    [QuasiSeparated pB] (R₀ : Subalgebra k ℂ) (h : R₀.FG)
    (M N : LB (pullback pB (spMap (algebraMap k R₀)))) (hM : M.IsLB) (hN : N.IsLB)
    (j₀ : pullback pB (spMap (algebraMap k ℂ)) ⟶ pullback pB (spMap (algebraMap k R₀)))
    (h₁ : j₀ ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j₀ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R₀.val.toRingHom)
    (H : LBIso (M.pull j₀) (N.pull j₀)) :
    ∃ (R : Subalgebra k ℂ) (hR : R₀ ≤ R)
      (i : pullback pB (spMap (algebraMap k R)) ⟶ pullback pB (spMap (algebraMap k R₀))), R.FG ∧
      i ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (Subalgebra.inclusion hR).toRingHom ∧
      LBIso (M.pull i) (N.pull i) := by sorry
