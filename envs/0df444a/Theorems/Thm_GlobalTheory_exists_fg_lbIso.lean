-- Prove2me | Theorems.Thm_GlobalTheory_exists_fg_lbIso
-- name    : GlobalTheory.exists_fg_lbIso
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:06:53.969046+00:00
-- url     : https://prove2.me/theorems/f1b6a18f-953b-4cf8-8530-d3a1f066f86e
-- title:
--   Global Theory: exists fg lb Iso
-- statement:
--   The Global Theory construction uses the exists fg lb Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L448-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L448-L469

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
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
variable {R₀ : Subalgebra k C}
variable {B : Scheme.{0}} (pB : B ⟶ Sp k)

theorem GlobalTheory.exists_fg_lbIso [QuasiCompact pB] [QuasiSeparated pB] (h : R₀.FG)
    (M N : LB (pullback pB (spMap (algebraMap k R₀)))) (hM : M.IsLB) (hN : N.IsLB)
    (H : LBIso (M.pull (baseChangeMap pB R₀.val)) (N.pull (baseChangeMap pB R₀.val))) :
    ∃ (R : Subalgebra k C) (hR : R₀ ≤ R), R.FG ∧
      LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR)))
        (N.pull (baseChangeMap pB (Subalgebra.inclusion hR))) := by sorry
