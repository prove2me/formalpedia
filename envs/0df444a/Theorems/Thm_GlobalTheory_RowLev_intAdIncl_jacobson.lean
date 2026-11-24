-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_intAdIncl_jacobson
-- name    : GlobalTheory.RowLev.intAdIncl_jacobson
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:36.580637+00:00
-- url     : https://prove2.me/theorems/9c6dffdc-aa1f-436c-bfd9-b763059ace55
-- title:
--   Row Lev: int Ad Incl jacobson
-- statement:
--   The Row Lev construction uses the int Ad Incl jacobson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralAdeleIdealOfIdealPrincipalAndInter.lean#L148-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralAdeleIdealOfIdealPrincipalAndInter.lean#L148-L154

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

theorem GlobalTheory.RowLev.intAdIncl_jacobson {x : intAd F} (hx : x ∈ Ideal.jacobson (⊥ : Ideal (intAd F))) :
    intAdIncl F E x ∈ Ideal.jacobson (⊥ : Ideal (IntAf F E)) := by sorry
