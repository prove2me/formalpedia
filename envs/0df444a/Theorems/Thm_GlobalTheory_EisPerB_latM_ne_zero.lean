-- Prove2me | Theorems.Thm_GlobalTheory_EisPerB_latM_ne_zero
-- name    : GlobalTheory.EisPerB.latM_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:58:22.520399+00:00
-- url     : https://prove2.me/theorems/7efc8cdb-1149-4f05-b656-dc36eb8ef6be
-- title:
--   Eis Per B: lat M ne zero
-- statement:
--   The Eis Per B construction uses the lat M ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeSumEqConeSum.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeSumEqConeSum.lean#L16-L18

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

theorem GlobalTheory.EisPerB.latM_ne_zero (𝔞 : Frac F) : latM 𝔞 ≠ 0 := by sorry
