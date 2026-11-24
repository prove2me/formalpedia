-- Prove2me | Theorems.Thm_GlobalTheory_EisPerB_eisTerm_eq
-- name    : GlobalTheory.EisPerB.eisTerm_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:10.921604+00:00
-- url     : https://prove2.me/theorems/0fe6606e-4ea0-450f-889a-c972f23ad3a4
-- title:
--   Eis Per B: eis Term eq
-- statement:
--   The Eis Per B construction uses the eis Term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeSumEqConeSum.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeSumEqConeSum.lean#L26-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemTraceDualSignedPositiveConeIffTotallyPositiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzConstantInverseDifferentEisensteinStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeSumEqConeSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.EisPerB
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.EisPerB.eisTerm_eq [IsTotallyReal F] (k : ℕ) (z : Emb F → ℂ) (a b : F) :
    eisTerm k 0 z (a, b) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
      lhsTerm k (fun τ => ((τ b : ℝ) : ℂ) * z τ) a := by sorry
