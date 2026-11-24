-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_eq_smul_of_top
-- name    : GlobalTheory.CompanionTheory.KLowSpan.eq_smul_of_top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:39.13404+00:00
-- url     : https://prove2.me/theorems/70acbdb4-82c4-4338-8bc8-bc5617504b07
-- title:
--   KLow Span: eq smul of top
-- statement:
--   The KLow Span construction uses the eq smul of top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InnerEqZeroOfWeight.lean#L213-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InnerEqZeroOfWeight.lean#L213-L229

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

theorem GlobalTheory.CompanionTheory.KLowSpan.eq_smul_of_top (hF : KRel ε E) (hU : KUnit ε E) (hv0 : v ≠ 0) (hv : IsWeight E μ v) {x : V}
    (hx : x ∈ kLowSpan ε E v) (hμ : IsWeight E μ x) : ∃ c : ℂ, x = c • v := by sorry
