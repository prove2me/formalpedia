-- Prove2me | Theorems.Thm_GlobalTheory_xClasses_index
-- name    : GlobalTheory.xClasses_index
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:50.737467+00:00
-- url     : https://prove2.me/theorems/e8bf661b-ed44-4333-8a5a-432435bc6013
-- title:
--   Global Theory: x Classes index
-- statement:
--   The Global Theory construction uses the x Classes index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/XClassesDenom.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/XClassesDenom.lean#L11-L26

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_XClassesDenom
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
open GlobalTheory

theorem GlobalTheory.xClasses_index {K : Type} [Field K] [NumberField K] (I J : Ideal (𝓞 K)) (a : 𝓞 K)
    (ha : a ≠ 0) (h : Ideal.span {a} = I * J) :
    ((Ideal.span {a}).toAddSubgroup.addSubgroupOf J.toAddSubgroup).index = Ideal.absNorm I := by sorry
