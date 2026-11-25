-- Prove2me | Theorems.Thm_GlobalTheory_Spread_dominant_of_compatible
-- name    : GlobalTheory.Spread.dominant_of_compatible
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:36:25.973863+00:00
-- url     : https://prove2.me/theorems/4d3fbf76-c817-52db-8569-6e565e864eb1
-- title:
--   Spread: dominant of compatible
-- statement:
--   The Spread construction uses the dominant of compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L299-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/MorphismsSpreadOutToFgSubalgebra.lean#L299-L305

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
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)

theorem GlobalTheory.Spread.dominant_of_compatible (R : Subalgebra k A)
    {j : pullback pB (spMap (algebraMap k A)) ⟶ pullback pB (spMap (algebraMap k R))}
    (h₁ : j ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap R.val.toRingHom) :
    QuasiCompact j ∧ IsSchemeTheoreticallyDominant j := by sorry
