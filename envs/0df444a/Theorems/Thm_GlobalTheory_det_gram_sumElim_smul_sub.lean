-- Prove2me | Theorems.Thm_GlobalTheory_det_gram_sumElim_smul_sub
-- name    : GlobalTheory.det_gram_sumElim_smul_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:53.903846+00:00
-- url     : https://prove2.me/theorems/b474e05b-40e2-44da-aad0-ba4e44d56b72
-- title:
--   Global Theory: det gram sum Elim smul sub
-- statement:
--   The Global Theory construction uses the det gram sum Elim smul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetGramSumElimSmulSub.lean#L71-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetGramSumElimSmulSub.lean#L71-L84

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramSumElimSmulSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open GlobalTheory
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem GlobalTheory.det_gram_sumElim_smul_sub {n : ℕ} (f f' : Fin n → V) (c : F) :
    (H.gram (Sum.elim f fun a => algebraMap F E c • (f' a - f a))).det
      = algebraMap F E c ^ (2 * n) * (H.gram (Sum.elim f f')).det := by sorry
