-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_cdom_of_weight
-- name    : GlobalTheory.CompanionTheory.KLowSpan.cdom_of_weight
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:33.570963+00:00
-- url     : https://prove2.me/theorems/b315b9ae-03c4-422a-90f8-d94e7c93194d
-- title:
--   KLow Span: cdom of weight
-- statement:
--   The KLow Span construction uses the cdom of weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InnerEqZeroOfWeight.lean#L205-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InnerEqZeroOfWeight.lean#L205-L211

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}

theorem GlobalTheory.CompanionTheory.KLowSpan.cdom_of_weight (hF : KRel ε E) (hU : KUnit ε E) (hv : IsWeight E μ v) {ν : Fin n → ℝ} {x : V}
    (hx : x ∈ kLowSpan ε E v) (hx0 : x ≠ 0) (hν : IsWeight E ν x) : PI.UpqRep.CDom ε ν μ := by sorry
