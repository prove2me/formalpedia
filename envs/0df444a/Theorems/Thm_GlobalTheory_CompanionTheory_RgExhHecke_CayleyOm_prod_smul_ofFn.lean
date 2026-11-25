-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_prod_smul_ofFn
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.prod_smul_ofFn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:18.461105+00:00
-- url     : https://prove2.me/theorems/d0aaa8ac-e50f-428c-a37c-81a222cccf20
-- title:
--   Cayley Om: prod smul of Fn
-- statement:
--   The Cayley Om construction uses the prod smul of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L112-L118

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.prod_smul_ofFn {m : ℕ} (s : ℂ) (f : Fin m → A) :
    (List.ofFn fun i => s • f i).prod = s ^ m • (List.ofFn f).prod := by sorry
