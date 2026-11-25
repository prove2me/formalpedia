-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_minor_expand
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.minor_expand
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:16.193137+00:00
-- url     : https://prove2.me/theorems/f9a47999-b7a0-5f67-9bbd-16ce1efc60fc
-- title:
--   Rg Exh Hecke: minor expand
-- statement:
--   The Rg Exh Hecke construction uses the minor expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L70-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L70-L80

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
variable {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {q : ℕ}
  (R C : Fin (q + 2) → Fin n) (x : ℂ) (f : Fin n → V) (d : Fin n)

theorem GlobalTheory.CompanionTheory.RgExhHecke.minor_expand (i : Fin (q + 2)) (l : Fin (q + 1)) :
    cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) =
      ∑ k : Fin (q + 1), ((-1 : ℂ) ^ (k : ℕ)) •
        capEntry E (x - 1) (R (i.succAbove k)) (C 0) (dbl E R C x f i k l) := by sorry
