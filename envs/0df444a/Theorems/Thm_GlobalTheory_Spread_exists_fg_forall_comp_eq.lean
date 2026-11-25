-- Prove2me | Theorems.Thm_GlobalTheory_Spread_exists_fg_forall_comp_eq
-- name    : GlobalTheory.Spread.exists_fg_forall_comp_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:33.745405+00:00
-- url     : https://prove2.me/theorems/e45baf10-83c1-478a-be8b-3d1a6779ac75
-- title:
--   Spread: exists fg forall comp eq
-- statement:
--   The Spread construction uses the exists fg forall comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L184-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L184-L196

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

theorem GlobalTheory.Spread.exists_fg_forall_comp_eq [QuasiCompact pB] [QuasiSeparated pB]
    [LocallyOfFinitePresentation pZ] {ι : Type*} [Finite ι]
    (φ : ι → (pullback pB (spMap (algebraMap k A)) ⟶ Z))
    (hφ : ∀ i, φ i ≫ pZ = pullback.fst _ _ ≫ pB) (R₀ : Subalgebra k A) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k A) (ψ : ι → (pullback pB (spMap (algebraMap k R)) ⟶ Z)),
      R.FG ∧ R₀ ≤ R ∧ ∀ i, ψ i ≫ pZ = pullback.fst _ _ ≫ pB ∧ bcMap pB R.val ≫ ψ i = φ i := by sorry
