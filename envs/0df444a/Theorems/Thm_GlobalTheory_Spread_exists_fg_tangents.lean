-- Prove2me | Theorems.Thm_GlobalTheory_Spread_exists_fg_tangents
-- name    : GlobalTheory.Spread.exists_fg_tangents
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:29:08.611391+00:00
-- url     : https://prove2.me/theorems/255fd490-aa15-4126-8fbf-e68abfa8fe6b
-- title:
--   Spread: exists fg tangents
-- statement:
--   The Spread construction uses the exists fg tangents property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L250-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L250-L286

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
open Chart

theorem GlobalTheory.Spread.exists_fg_tangents [LocallyOfFinitePresentation pZ] {ι : Type*} [Finite ι]
    (v : ι → (Sp (DualNumber A) ⟶ Z))
    (hv : ∀ i, v i ≫ pZ = spMap (algebraMap k (DualNumber A)))
    (R₀ : Subalgebra k A) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k A) (w : ι → (Sp (DualNumber R) ⟶ Z)), R.FG ∧ R₀ ≤ R ∧
      ∀ i, w i ≫ pZ = spMap (algebraMap k (DualNumber R)) ∧
        spMap (dualMapR R.val.toRingHom) ≫ w i = v i := by sorry
