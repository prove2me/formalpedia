-- Prove2me | Theorems.Thm_GlobalTheory_Spread_tangent_ext
-- name    : GlobalTheory.Spread.tangent_ext
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:19.631295+00:00
-- url     : https://prove2.me/theorems/7dd8f709-62aa-479a-b7ab-cf37e4848e09
-- title:
--   Spread: tangent ext
-- statement:
--   The Spread construction uses the tangent ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L288-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L288-L291

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

theorem GlobalTheory.Spread.tangent_ext {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (hf : Function.Injective f)
    {S : Scheme.{0}} (s : Z ⟶ S) [IsSeparated s] {a b : Sp (DualNumber R) ⟶ Z} (h : a ≫ s = b ≫ s)
    (hab : spMap (dualMapR f) ≫ a = spMap (dualMapR f) ≫ b) : a = b := by sorry
