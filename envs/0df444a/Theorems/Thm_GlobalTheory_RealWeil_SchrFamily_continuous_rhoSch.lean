-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_SchrFamily_continuous_rhoSch
-- name    : GlobalTheory.RealWeil.SchrFamily.continuous_rhoSch
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:16:54.02413+00:00
-- url     : https://prove2.me/theorems/db51a3c2-3558-48f8-95f3-f20f75bb3ae5
-- title:
--   Schr Family: continuous rho Sch
-- statement:
--   The Schr Family construction uses the continuous rho Sch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchrodingerRepSchwartzPolynomialBound.lean#L87-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchrodingerRepSchwartzPolynomialBound.lean#L87-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.SchrFamily
variable {l : Type} [Fintype l]

theorem GlobalTheory.RealWeil.SchrFamily.continuous_rhoSch (g : Sch l) : Continuous fun w => rhoSch w g := by sorry
