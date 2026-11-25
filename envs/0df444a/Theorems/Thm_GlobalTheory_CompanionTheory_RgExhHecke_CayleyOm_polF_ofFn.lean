-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_polF_ofFn
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.polF_ofFn
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:15.53487+00:00
-- url     : https://prove2.me/theorems/c9441f80-5dcb-4e59-9b5f-ba6fbfda80c8
-- title:
--   Cayley Om: pol F of Fn
-- statement:
--   The Cayley Om construction uses the pol F of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L82-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L82-L88

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.polF_ofFn {m : ℕ} (f : Fin m → ℂ → A) (h : ∀ i, PolF (f i)) :
    PolF fun y => (List.ofFn fun i => f i y).prod := by sorry
