-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_cayleyHam_of
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:10:21.669667+00:00
-- url     : https://prove2.me/theorems/a9b64f92-0f72-4d50-b6e2-c3ebadb49745
-- title:
--   Cayley Om: cayley Ham of
-- statement:
--   The Cayley Om construction uses the cayley Ham of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L188-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L188-L247

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam_of (H : QdetTens) : CayleyHam := by sorry
