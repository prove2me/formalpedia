-- Prove2me | Theorems.Thm_GlobalTheory_appTop_comp_spMap
-- name    : GlobalTheory.appTop_comp_spMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:14:35.506304+00:00
-- url     : https://prove2.me/theorems/d6e4d9cb-6381-50c6-b994-25bf3bbb83d9
-- title:
--   Global Theory: app Top comp sp Map
-- statement:
--   The Global Theory construction uses the app Top comp sp Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L395-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L395-L400

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

theorem GlobalTheory.appTop_comp_spMap {T : Scheme.{0}} {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A')
    (f : T ⟶ Sp A') (x : A) :
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (f ≫ spMap φ).appTop).hom x =
      ((Scheme.ΓSpecIso (.of A')).inv ≫ f.appTop).hom (φ x) := by sorry
