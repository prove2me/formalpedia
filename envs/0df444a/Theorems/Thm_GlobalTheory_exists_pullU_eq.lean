-- Prove2me | Theorems.Thm_GlobalTheory_exists_pullU_eq
-- name    : GlobalTheory.exists_pullU_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:05:48.385992+00:00
-- url     : https://prove2.me/theorems/3e38881f-289c-4bc8-aef0-3b781dd7afd2
-- title:
--   Global Theory: exists pull U eq
-- statement:
--   The Global Theory construction uses the exists pull U eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L151-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L151-L158

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

theorem GlobalTheory.exists_pullU_eq {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (s t : Γ(D.obj i, U)ˣ)
    (h : ∀ y : X, π i y ∈ U → gm (π i) y U s = gm (π i) y U t) :
    ∃ (j : I) (f : j ⟶ i), pullU (D.map f) U s = pullU (D.map f) U t := by sorry
