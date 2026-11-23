-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_discrete_latOf
-- name    : GlobalTheory.LipschitzTR.discrete_latOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:44.317256+00:00
-- url     : https://prove2.me/theorems/7c05940b-e46c-4444-bba7-eb829754af48
-- title:
--   Lipschitz TR: discrete lat Of
-- statement:
--   The Lipschitz TR construction uses the discrete lat Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiscreteTopologyFractionalIdealRealLatticeImage.lean#L23-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiscreteTopologyFractionalIdealRealLatticeImage.lean#L23-L51

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

theorem GlobalTheory.LipschitzTR.discrete_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), DiscreteTopology (latOf N) := by sorry
