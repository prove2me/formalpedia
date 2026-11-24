-- Prove2me | Theorems.Thm_GlobalTheory_cm_discr_sq
-- name    : GlobalTheory.cm_discr_sq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:04.964793+00:00
-- url     : https://prove2.me/theorems/dae2ab98-a94e-46e8-8f83-497ab428a18c
-- title:
--   Global Theory: cm discr sq
-- statement:
--   The Global Theory construction uses the cm discr sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SubMemDifferentIdeal.lean#L96-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SubMemDifferentIdeal.lean#L96-L110

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SubMemDifferentIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open NumberField Module Matrix
open scoped ENNReal

theorem GlobalTheory.cm_discr_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [StarRing E] [Algebra F E], _root_.Formalism.BasicNotions.CMData F E → |discr E| = discr F ^ 2 ∧
      Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F))) =
        (discr F).natAbs ^ 2 := by sorry
