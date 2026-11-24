-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_intAdIncl_isIntegral
-- name    : GlobalTheory.RowLev.intAdIncl_isIntegral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:33:11.844474+00:00
-- url     : https://prove2.me/theorems/3578df7d-751f-407d-be3f-2e0df6d21900
-- title:
--   Row Lev: int Ad Incl is Integral
-- statement:
--   The Row Lev construction uses the int Ad Incl is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralAdeleIdealOfIdealPrincipalAndInter.lean#L123-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralAdeleIdealOfIdealPrincipalAndInter.lean#L123-L146

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open Formalism.UG Formalism.UG.P Inhab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.RowLev.intAdIncl_isIntegral : (intAdIncl F E).IsIntegral := by sorry
