-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_span_range_remb
-- name    : GlobalTheory.LipschitzTR.span_range_remb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:13:02.822507+00:00
-- url     : https://prove2.me/theorems/189fdfb1-524a-496b-a275-74628600427a
-- title:
--   Lipschitz TR: span range remb
-- statement:
--   The Lipschitz TR construction uses the span range remb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsZLatticeFractionalIdealRealLatticeImage.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsZLatticeFractionalIdealRealLatticeImage.lean#L8-L35

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsZLatticeFractionalIdealRealLatticeImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.LipschitzTR

theorem GlobalTheory.LipschitzTR.span_range_remb (F : Type) [Field F] [NumberField F] :
    Submodule.span ℝ (Set.range (remb F)) = ⊤ := by sorry
