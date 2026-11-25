-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_sum_pair_swap
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.sum_pair_swap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:49.735798+00:00
-- url     : https://prove2.me/theorems/969dc3b1-c363-453b-a7a7-cfd279c2b802
-- title:
--   Rg Exh Hecke: sum pair swap
-- statement:
--   The Rg Exh Hecke construction uses the sum pair swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L29-L36

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_WhittakerZeroStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli CompanionTheory.RgExh
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.RgExhHecke.sum_pair_swap {M : Type*} [AddCommMonoid M] {q : ℕ} (Φ : Fin (q + 2) → Fin (q + 1) → M) :
    ∑ i, ∑ k, Φ i k = ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), Φ (i.succAbove k) (k.predAbove i) := by sorry
