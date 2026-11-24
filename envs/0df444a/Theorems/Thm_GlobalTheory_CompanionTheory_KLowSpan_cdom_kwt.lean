-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_cdom_kwt
-- name    : GlobalTheory.CompanionTheory.KLowSpan.cdom_kwt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:34.686343+00:00
-- url     : https://prove2.me/theorems/b246df14-c064-4054-88ef-0be43640e747
-- title:
--   KLow Span: cdom kwt
-- statement:
--   The KLow Span construction uses the cdom kwt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InnerEqZeroOfWeight.lean#L151-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InnerEqZeroOfWeight.lean#L151-L173

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil


set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KLowSpan
variable {n : ℕ} {ε : Fin n → Bool}
variable {U : Type} [AddCommGroup U] [Module ℂ U]
variable {F : Fin n → Fin n → Module.End ℂ U} {μ : Fin n → ℝ} {w : U}

theorem GlobalTheory.CompanionTheory.KLowSpan.cdom_kwt (μ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), KLower ε l → PI.UpqRep.CDom ε (kwt μ l) μ := by sorry
