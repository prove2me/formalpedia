-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_summable_prod_wt
-- name    : GlobalTheory.LipschitzTR.LhsSum.summable_prod_wt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:11:26.124253+00:00
-- url     : https://prove2.me/theorems/a2e31224-a4c7-45e1-b34d-077e0b88524e
-- title:
--   Lhs Sum: summable prod wt
-- statement:
--   The Lhs Sum construction uses the summable prod wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummand.lean#L111-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummand.lean#L111-L128

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
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
open GlobalTheory GlobalTheory.LipschitzTR GlobalTheory.LipschitzTR.LhsSum
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.LipschitzTR.LhsSum.summable_prod_wt (ι : Type) [Fintype ι] [DecidableEq ι] :
    Summable (fun n : ι → ℤ => ∏ i, wt (n i)) := by sorry
