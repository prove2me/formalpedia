-- Prove2me | Theorems.Thm_GlobalTheory_PlaceRestrict_exists_gauss_variables
-- name    : GlobalTheory.PlaceRestrict.exists_gauss_variables
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:05:47.276472+00:00
-- url     : https://prove2.me/theorems/1fbe5c2e-a564-5d99-85d9-fb7ddf0480fc
-- title:
--   Place Restrict: exists gauss variables
-- statement:
--   The Place Restrict construction uses the exists gauss variables property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/PlacesRestrictInjective.lean#L127-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/PlacesRestrictInjective.lean#L127-L287

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

theorem GlobalTheory.PlaceRestrict.exists_gauss_variables (d : Data K ι Ω WT A) (hd : d.AxH 𝒜)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) (j0 : Fin (d.N + 1))
    (hw0 : d.w j0 c ≠ 0) :
    ∃ t : SVar d.D d.N → OmS (Ω c) d.D d.N,
      (∀ P : MvPolynomial (SVar d.D d.N) (Ω c), ∃ Q : MvPolynomial (SVar d.D d.N) (Ω c),
        MvPolynomial.aeval t Q = algebraMap _ (OmS (Ω c) d.D d.N) P) ∧
      ∀ w ∈ d.PlOver la c, (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) →
        ∃ ht : ∀ s, t s ∈ vRing w,
          letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
          AlgebraicIndependent
            (ResidueField ((vRing w).comap (algebraMap (Ω c) (OmS (Ω c) d.D d.N))))
            (fun s => residue (vRing w) ⟨t s, ht s⟩) := by sorry
