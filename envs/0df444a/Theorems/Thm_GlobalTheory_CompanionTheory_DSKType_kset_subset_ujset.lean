-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSKType_kset_subset_ujset
-- name    : GlobalTheory.CompanionTheory.DSKType.kset_subset_ujset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:10.527169+00:00
-- url     : https://prove2.me/theorems/70cbd5dc-a357-476e-b68b-4ddd2ce2aac4
-- title:
--   DSKType: kset subset ujset
-- statement:
--   The DSKType construction uses the kset subset ujset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KsetSubsetUjset.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KsetSubsetUjset.lean#L11-L18

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KsetSubsetUjset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSKType
open CompanionTheory.D.DSIC PI.UpqRep

theorem GlobalTheory.CompanionTheory.DSKType.kset_subset_ujset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by sorry
