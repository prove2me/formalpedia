-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_key_identity
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.key_identity
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:39.854875+00:00
-- url     : https://prove2.me/theorems/31173339-8701-50a4-a332-b5081406f0e6
-- title:
--   Rg Exh Hecke: key identity
-- statement:
--   The Rg Exh Hecke construction uses the key identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L82-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L82-L137

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.key_identity :
    (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • capEntry E x (R i) (C 0)
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if d = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0)) +
      (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • (if d = R i then
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if C 0 = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) else 0)) =
    ∑ i : Fin (q + 2), ∑ l : Fin (q + 1), if d = R i then
      ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) •
        cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) else 0 := by sorry
