-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_SchrFamily_rhoSch_eq
-- name    : GlobalTheory.RealWeil.SchrFamily.rhoSch_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:17:08.878772+00:00
-- url     : https://prove2.me/theorems/d81ba5f6-73e7-44f3-8ddc-5fc47b89c4a5
-- title:
--   Schr Family: rho Sch eq
-- statement:
--   The Schr Family construction uses the rho Sch eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchrodingerRepSchwartzPolynomialBound.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchrodingerRepSchwartzPolynomialBound.lean#L22-L29

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

theorem GlobalTheory.RealWeil.SchrFamily.rhoSch_eq (w : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w g = SchwartzMap.smulLeftCLM ℂ
      (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2))
      (SchwartzMap.compSubConstCLM ℂ (-pPart w) g) := by sorry
