-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_cminor_tensE_apply
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.cminor_tensE_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:02.696327+00:00
-- url     : https://prove2.me/theorems/9280c48e-a031-5135-b8fc-323f0f84ae49
-- title:
--   Rg Exh Hecke: cminor tens E apply
-- statement:
--   The Rg Exh Hecke construction uses the cminor tens E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L141-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L141-L185

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.cminor_tensE_apply (X : GMod n) (q : ℕ) : ∀ (R C : Fin (q + 1) → Fin n) (x : ℂ)
    (f : Fin n → X.V) (d : Fin n),
    cminor (tensE X) R C x f d = cminor X.E R C x (f d) +
      ∑ i : Fin (q + 1), ∑ j : Fin (q + 1), if d = R i then
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          cminor X.E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) (f (C j)) else 0 := by sorry
