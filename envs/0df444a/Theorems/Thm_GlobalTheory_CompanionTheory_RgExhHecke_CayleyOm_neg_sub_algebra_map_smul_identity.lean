-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_neg_sub_algebra_map_smul_identity
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.neg_sub_algebra_map_smul_identity
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:11:27.059248+00:00
-- url     : https://prove2.me/theorems/ddae40e7-b26b-403e-90cc-70c297b33d75
-- title:
--   Cayley Om: neg sub algebra map smul identity
-- statement:
--   The Cayley Om construction uses the neg sub algebra map smul identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L183-L186

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
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.neg_sub_algebra_map_smul_identity {A : Type*} [Ring A] [Algebra ℂ A] (w : A) (x c : ℂ) :
    -w - algebraMap ℂ A c + algebraMap ℂ A x = (-1 : ℂ) • (w - (x - c) • (1 : A)) := by sorry
