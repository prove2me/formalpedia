-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzCovol_measurePreserving_toMixed
-- name    : GlobalTheory.LipschitzCovol.measurePreserving_toMixed
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:11:55.821116+00:00
-- url     : https://prove2.me/theorems/87325c75-a138-4974-80c1-21e0833e1887
-- title:
--   Lipschitz Covol: measure Preserving to Mixed
-- statement:
--   The Lipschitz Covol construction uses the measure Preserving to Mixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFractionalIdealRealLatticeImage.lean#L52-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFractionalIdealRealLatticeImage.lean#L52-L72

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
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
noncomputable section
open GlobalTheory GlobalTheory.LipschitzCovol
open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem GlobalTheory.LipschitzCovol.measurePreserving_toMixed :
    MeasurePreserving (toMixed (F := F)).toContinuousLinearEquiv volume volume := by sorry
