-- Prove2me | Theorems.Thm_GlobalTheory_Spread_eq_bcMap
-- name    : GlobalTheory.Spread.eq_bcMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:25.358587+00:00
-- url     : https://prove2.me/theorems/bc752d32-f0d1-4c21-a904-a220435736cc
-- title:
--   Spread: eq bc Map
-- statement:
--   The Spread construction uses the eq bc Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L66-L72

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
variable {R R' A : Type} [CommRing R] [CommRing R'] [CommRing A] [Algebra k R] [Algebra k R']
  [Algebra k A]

theorem GlobalTheory.Spread.eq_bcMap (f : R →ₐ[k] A)
    {j : pullback pB (spMap (algebraMap k A)) ⟶ pullback pB (spMap (algebraMap k R))}
    (h₁ : j ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap f.toRingHom) : j = bcMap pB f := by sorry
