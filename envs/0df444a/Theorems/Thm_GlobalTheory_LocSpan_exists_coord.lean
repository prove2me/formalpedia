-- Prove2me | Theorems.Thm_GlobalTheory_LocSpan_exists_coord
-- name    : GlobalTheory.LocSpan.exists_coord
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:11.090871+00:00
-- url     : https://prove2.me/theorems/8dfee951-b5d9-40c7-99f4-a417e69b94cd
-- title:
--   Loc Span: exists coord
-- statement:
--   The Loc Span construction uses the exists coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIntegersLocalisationIffSumCmData.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIntegersLocalisationIffSumCmData.lean#L40-L47

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocSpan
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem GlobalTheory.LocSpan.exists_coord (hc : Formalism.BasicNotions.CMData F E) (θ : E) (hθ : θ - star θ ≠ 0) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ := by sorry
