-- Prove2me | Theorems.Thm_GlobalTheory_Spread_exists_fg_comp_eq
-- name    : GlobalTheory.Spread.exists_fg_comp_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:27:54.535623+00:00
-- url     : https://prove2.me/theorems/5320e0a7-c7dc-4b49-8027-9fe07328d6e5
-- title:
--   Spread: exists fg comp eq
-- statement:
--   The Spread construction uses the exists fg comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L163-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L163-L173

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

theorem GlobalTheory.Spread.exists_fg_comp_eq [QuasiCompact pB] [QuasiSeparated pB] [LocallyOfFinitePresentation pZ]
    (φ : pullback pB (spMap (algebraMap k A)) ⟶ Z) (hφ : φ ≫ pZ = pullback.fst _ _ ≫ pB) :
    ∃ (R : Subalgebra k A) (ψ : pullback pB (spMap (algebraMap k R)) ⟶ Z),
      R.FG ∧ ψ ≫ pZ = pullback.fst _ _ ≫ pB ∧ bcMap pB R.val ≫ ψ = φ := by sorry
