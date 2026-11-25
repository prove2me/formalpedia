-- Prove2me | Theorems.Thm_GlobalTheory_HeckeObjectExamples_isCMExt_of_isCMField
-- name    : GlobalTheory.HeckeObjectExamples.isCMExt_of_isCMField
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:40.985065+00:00
-- url     : https://prove2.me/theorems/1a9c82d2-1f39-4fb3-b842-bdef857036f2
-- title:
--   Hecke Object Examples: is CMExt of is CMField
-- statement:
--   The Hecke Object Examples construction uses the is CMExt of is CMField property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LfacDenominatorNeZero.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LfacDenominatorNeZero.lean#L48-L51

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

theorem GlobalTheory.HeckeObjectExamples.isCMExt_of_isCMField (K : Type) [Field K] [NumberField K] [IsCMField K] :
    IsCMExt (maximalRealSubfield K) K (IsCMField.complexConj K).toAlgHom := by sorry
