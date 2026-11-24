-- Prove2me | Theorems.Thm_GlobalTheory_LevelCompat_corr_of_pmaps
-- name    : GlobalTheory.LevelCompat.corr_of_pmaps
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:03:19.233843+00:00
-- url     : https://prove2.me/theorems/78fe7c9a-85f4-4e34-886a-61fa3e230d62
-- title:
--   Level Compat: corr of pmaps
-- statement:
--   The Level Compat construction uses the corr of pmaps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GtCoordCompatOfPull.lean#L45-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GtCoordCompatOfPull.lean#L45-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.LevelCompat
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LevelCompat.corr_of_pmaps {X X' Y₀ Y₁ Y₀' Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {ε : K → ℤ}
    {φ₀ : K → (Y₀ ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₀' : K → (Y₀' ⟶ X')} {φ₁' : K → (Y₁' ⟶ X')}
    {t₀ : LB.Gen (LB.LinComb L φ₀ ε)} {t₁ : LB.Gen (LB.LinComb L φ₁ ε)}
    {t₀' : LB.Gen (LB.LinComb L' φ₀' ε)} {t₁' : LB.Gen (LB.LinComb L' φ₁' ε)}
    {h₀ : Y₀' ⟶ Y₀} {h₁ : Y₁' ⟶ Y₁} {m : Y₀ ⟶ Y₁} {m' : Y₀' ⟶ Y₁'} (hm : m' ≫ h₁ = h₀ ≫ m)
    (c₀ : ∀ k, φ₀' k ≫ F = h₀ ≫ φ₀ k) (c₁ : ∀ k, φ₁' k ≫ F = h₁ ≫ φ₁ k) (c' : ∀ k, m' ≫ φ₁' k = φ₀' k)
    (H₀ : PMaps w φ₀' φ₀ ε t₀' t₀ h₀) (H₁ : PMaps w φ₁' φ₁ ε t₁' t₁ h₁)
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t₁ m) t₀) :
    LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ t₁' m') t₀' := by sorry
