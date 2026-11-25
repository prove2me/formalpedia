-- Prove2me | Theorems.Thm_GlobalTheory_exists_units_of_isLimit
-- name    : GlobalTheory.exists_units_of_isLimit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:09:44.130853+00:00
-- url     : https://prove2.me/theorems/bfe196dc-31c1-45aa-bc96-18536d7717c2
-- title:
--   Global Theory: exists units of is Limit
-- statement:
--   The Global Theory construction uses the exists units of is Limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L162-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L162-L218

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

theorem GlobalTheory.exists_units_of_isLimit {i : I} [QuasiSeparatedSpace (D.obj i)] {A : Type} [Finite A]
    (V : A → (D.obj i).Opens) (hV : ∀ a, IsAffineOpen (V a)) (G : ∀ a b, Γ(D.obj i, V a ⊓ V b)ˣ)
    (s : ∀ a, Γ(X, π i ⁻¹ᵁ V a)ˣ)
    (hs : ∀ a b (y : X), y ∈ π i ⁻¹ᵁ V a → y ∈ π i ⁻¹ᵁ V b →
      gm (𝟙 X) y _ (s a) = gm (π i) y _ (G a b) * gm (𝟙 X) y _ (s b)) :
    ∃ (j : I) (f : j ⟶ i) (u : ∀ a, Γ(D.obj j, D.map f ⁻¹ᵁ V a)ˣ),
      ∀ a b (y : D.obj j), y ∈ D.map f ⁻¹ᵁ V a → y ∈ D.map f ⁻¹ᵁ V b →
        gm (𝟙 _) y _ (u a) = gm (D.map f) y _ (G a b) * gm (𝟙 _) y _ (u b) := by sorry
