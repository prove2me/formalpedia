-- Prove2me | Theorems.Thm_GlobalTheory_Spread_hom_ext_bcMap
-- name    : GlobalTheory.Spread.hom_ext_bcMap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:38:21.921805+00:00
-- url     : https://prove2.me/theorems/f0d5fd51-a443-4af3-95a7-4af8ac2fa5e3
-- title:
--   Spread: hom ext bc Map
-- statement:
--   The Spread construction uses the hom ext bc Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L211-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L211-L216

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

theorem GlobalTheory.Spread.hom_ext_bcMap [Flat pB] {R : Type} [CommRing R] [Algebra k R] (f : R →ₐ[k] A)
    (hf : Function.Injective f) {S : Scheme.{0}} (s : Z ⟶ S) [IsSeparated s]
    {a b : pullback pB (spMap (algebraMap k R)) ⟶ Z} (h : a ≫ s = b ≫ s)
    (hab : bcMap pB f ≫ a = bcMap pB f ≫ b) : a = b := by sorry
