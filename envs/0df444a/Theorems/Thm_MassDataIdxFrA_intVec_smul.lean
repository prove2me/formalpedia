-- Prove2me | Theorems.Thm_MassDataIdxFrA_intVec_smul
-- name    : MassDataIdxFrA.intVec_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:25.387897+00:00
-- url     : https://prove2.me/theorems/ea336ffb-1d17-5234-8ebf-67228d605b9f
-- title:
--   Mass Data Idx Fr A: int Vec smul
-- statement:
--   The Mass Data Idx Fr A construction uses the int Vec smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/CongSpanSingleIff.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/CongSpanSingleIff.lean#L20-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_CongSpanSingleIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxFrA
variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem MassDataIdxFrA.intVec_smul (c : O) {v : ι → F} (hv : IntVec O v) : IntVec O ((c : F) • v) := by sorry
