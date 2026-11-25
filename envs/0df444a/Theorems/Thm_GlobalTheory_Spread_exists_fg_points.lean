-- Prove2me | Theorems.Thm_GlobalTheory_Spread_exists_fg_points
-- name    : GlobalTheory.Spread.exists_fg_points
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:28:47.151051+00:00
-- url     : https://prove2.me/theorems/51817337-b924-4361-99b8-6a1385644a00
-- title:
--   Spread: exists fg points
-- statement:
--   The Spread construction uses the exists fg points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L218-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L218-L230

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Spread
variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
variable (A : Type) [CommRing A] [Algebra k A]
variable {A} (pZ : Z ⟶ Sp k)

theorem GlobalTheory.Spread.exists_fg_points [LocallyOfFinitePresentation pZ] {ι : Type*} [Finite ι]
    (x : ι → (Sp A ⟶ Z)) (hx : ∀ i, x i ≫ pZ = spMap (algebraMap k A))
    (R₀ : Subalgebra k A) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k A) (y : ι → (Sp R ⟶ Z)), R.FG ∧ R₀ ≤ R ∧
      ∀ i, y i ≫ pZ = spMap (algebraMap k R) ∧ spMap R.val.toRingHom ≫ y i = x i := by sorry
