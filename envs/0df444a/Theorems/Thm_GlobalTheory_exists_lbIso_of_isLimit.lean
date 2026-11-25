-- Prove2me | Theorems.Thm_GlobalTheory_exists_lbIso_of_isLimit
-- name    : GlobalTheory.exists_lbIso_of_isLimit
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:11:59.649576+00:00
-- url     : https://prove2.me/theorems/bb3aa876-1abc-5ae8-82d9-e76a1b4fb9bd
-- title:
--   Global Theory: exists lb Iso of is Limit
-- statement:
--   The Global Theory construction uses the exists lb Iso of is Limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L248-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L248-L288

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
variable {I : Type} [SmallCategory I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
include hc

theorem GlobalTheory.exists_lbIso_of_isLimit {i : I} [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (M N : LB (D.obj i)) (hM : M.IsLB) (hN : N.IsLB) (h : LBIso (M.pull (π i)) (N.pull (π i))) :
    ∃ (j : I) (f : j ⟶ i), LBIso (M.pull (D.map f)) (N.pull (D.map f)) := by sorry
