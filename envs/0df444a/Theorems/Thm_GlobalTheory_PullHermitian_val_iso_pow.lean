-- Prove2me | Theorems.Thm_GlobalTheory_PullHermitian_val_iso_pow
-- name    : GlobalTheory.PullHermitian.val_iso_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:58:47.904207+00:00
-- url     : https://prove2.me/theorems/c0e66572-33aa-4c48-8087-07d6e1298f25
-- title:
--   Pull Hermitian: val iso pow
-- statement:
--   The Pull Hermitian construction uses the val iso pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L98-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L98-L127

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

theorem GlobalTheory.PullHermitian.val_iso_pow {Y : Scheme.{0}} {L : LB X} {L' : LB Y} (f : X ⟶ Y) (m n : ℕ)
    (w : LB.Iso (lbPow (L'.pull f) m) (lbPow L n)) (hw : w.IsGen) (i i' : L.ι) (j j' : L'.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ L.U i') (hj : ⊤ ≤ (x ≫ f) ⁻¹ᵁ L'.U j)
    (hj' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ L'.U j') :
    valAt' x _ (w.s (idx f m n i j)).val *
        valAt' (x ≫ f) (L'.U j ⊓ L'.U j') (L'.g j j').val ^ m =
      valAt' x (L.U i ⊓ L.U i') (L.g i i').val ^ n * valAt' x _ (w.s (idx f m n i' j')).val := by sorry
