-- Prove2me | Theorems.Thm_GlobalTheory_PlacesOver_places_over_finset
-- name    : GlobalTheory.PlacesOver.places_over_finset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:30:03.608043+00:00
-- url     : https://prove2.me/theorems/41a8bfe7-3d5d-4d0a-b83e-29f52512250d
-- title:
--   Places Over: places over finset
-- statement:
--   The Places Over construction uses the places over finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFinsetPlacesOverFinsetPlaces.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFinsetPlacesOverFinsetPlaces.lean#L18-L26

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinsetPlacesOverFinsetPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.PlacesOver

theorem GlobalTheory.PlacesOver.places_over_finset (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ ∃ v ∈ S,
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by sorry
