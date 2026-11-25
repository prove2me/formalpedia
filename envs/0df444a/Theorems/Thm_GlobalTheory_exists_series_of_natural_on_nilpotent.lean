-- Prove2me | Theorems.Thm_GlobalTheory_exists_series_of_natural_on_nilpotent
-- name    : GlobalTheory.exists_series_of_natural_on_nilpotent
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:58:42.94754+00:00
-- url     : https://prove2.me/theorems/c83b7f5b-e2bd-429f-8af6-6380f8c0d5d3
-- title:
--   Global Theory: exists series of natural on nilpotent
-- statement:
--   The Global Theory construction uses the exists series of natural on nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSeriesOfNaturalOnNilpotent.lean#L76-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSeriesOfNaturalOnNilpotent.lean#L76-L135

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfNaturalOnNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.exists_series_of_natural_on_nilpotent :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) := by sorry
