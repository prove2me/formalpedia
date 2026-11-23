-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_wt_nonneg
-- name    : GlobalTheory.LipschitzTR.LhsSum.wt_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:32.716628+00:00
-- url     : https://prove2.me/theorems/162245c2-ec00-48ba-a229-51203b5e2f1b
-- title:
--   Lhs Sum: wt nonneg
-- statement:
--   The Lhs Sum construction uses the wt nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummand.lean#L93-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummand.lean#L93-L93

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

theorem GlobalTheory.LipschitzTR.LhsSum.wt_nonneg (m : ℤ) : 0 ≤ wt m := by sorry
