-- Prove2me | Theorems.Thm_GlobalTheory_HeckeObjectExamples_sigma_ne_id
-- name    : GlobalTheory.HeckeObjectExamples.sigma_ne_id
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:11:08.34979+00:00
-- url     : https://prove2.me/theorems/3a47eb27-2cf7-466a-8d0c-067822c22dc5
-- title:
--   Hecke Object Examples: sigma ne id
-- statement:
--   The Hecke Object Examples construction uses the sigma ne id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LfacDenominatorNeZero.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LfacDenominatorNeZero.lean#L17-L26

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LfacDenominatorNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn
open GlobalTheory GlobalTheory.HeckeObjectExamples
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.HeckeObjectExamples.sigma_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by sorry
