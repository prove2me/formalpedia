-- Prove2me | Theorems.Thm_GlobalTheory_PlaceRestrict_places_restrict_injective
-- name    : GlobalTheory.PlaceRestrict.places_restrict_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T17:17:44.115243+00:00
-- url     : https://prove2.me/theorems/f45eadb6-ea6a-4672-9436-2c0f2b418808
-- title:
--   Place Restrict: places restrict injective
-- statement:
--   The Place Restrict construction uses the places restrict injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/PlacesRestrictInjective.lean#L313-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/PlacesRestrictInjective.lean#L313-L339

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.PlaceRestrict
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem GlobalTheory.PlaceRestrict.places_restrict_injective (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT]
    (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)
    (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    (d.PlOver la c).Finite ∧ Set.InjOn (d.Wres c) (d.PlOver la c) ∧
      (∀ n : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ,
        ∃ g : Ω c, g ≠ 0 ∧ ∀ w ∈ d.PlOver la c, d.Wres c w g = n w) ∧
      (∀ G : WT, ∃ e ∈ 𝒜 c G, e ≠ 0 ∧ ∀ w ∈ d.PlOver la c, d.ord c (d.Wres c w) G e = 0) ∧
      ∀ w ∈ d.PlOver la c, ∀ a : Ω c, 0 ≤ d.Wres c w a →
        ∃ l : Ω c, (∀ w' ∈ d.PlOver la c, 0 ≤ d.Wres c w' l) ∧ 0 < d.Wres c w (a - l) := by sorry
