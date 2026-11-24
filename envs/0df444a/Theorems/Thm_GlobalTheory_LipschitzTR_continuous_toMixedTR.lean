-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_continuous_toMixedTR
-- name    : GlobalTheory.LipschitzTR.continuous_toMixedTR
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:10:59.560166+00:00
-- url     : https://prove2.me/theorems/422600e4-ca49-4a46-ae6e-afcb971b7893
-- title:
--   Lipschitz TR: continuous to Mixed TR
-- statement:
--   The Lipschitz TR construction uses the continuous to Mixed TR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiscreteTopologyFractionalIdealRealLatticeImage.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiscreteTopologyFractionalIdealRealLatticeImage.lean#L12-L15

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
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

theorem GlobalTheory.LipschitzTR.continuous_toMixedTR (F : Type) [Field F] [NumberField F] :
    Continuous (toMixedTR F) := by sorry
