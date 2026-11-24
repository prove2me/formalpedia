-- Prove2me | Theorems.Thm_GlobalTheory_SameZeroScheme_unit_eq_of_mul
-- name    : GlobalTheory.SameZeroScheme.unit_eq_of_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:54.659641+00:00
-- url     : https://prove2.me/theorems/47c403cb-1ad1-4f49-add1-8f5b4519d05e
-- title:
--   Same Zero Scheme: unit eq of mul
-- statement:
--   The Same Zero Scheme construction uses the unit eq of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsoLineBundleOfRegularPullbacksSameZeroScheme.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/IsoLineBundleOfRegularPullbacksSameZeroScheme.lean#L37-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsoLineBundleOfRegularPullbacksSameZeroScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SameZeroScheme

theorem GlobalTheory.SameZeroScheme.unit_eq_of_mul {R : Type*} [CommRing R] {a a' b b' : R} {c c' g₀ g₁ : Rˣ}
    (ha : a ∈ nonZeroDivisors R) (h : b = c * a) (h' : b' = c' * a') (hb : b = g₀ * b')
    (haa : a = g₁ * a') : c = g₀ ^ (1 : ℤ) * g₁ ^ (-1 : ℤ) * c' := by sorry
