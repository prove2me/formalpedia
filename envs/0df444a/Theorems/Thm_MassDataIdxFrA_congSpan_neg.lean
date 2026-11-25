-- Prove2me | Theorems.Thm_MassDataIdxFrA_congSpan_neg
-- name    : MassDataIdxFrA.congSpan_neg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:37.645677+00:00
-- url     : https://prove2.me/theorems/166ce2e4-89e2-45a5-9f1b-9ac496c1a748
-- title:
--   Mass Data Idx Fr A: cong Span neg
-- statement:
--   The Mass Data Idx Fr A construction uses the cong Span neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/CongSpanSingleIff.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/CongSpanSingleIff.lean#L38-L42

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
open Matrix
variable {F : Type} [Field F] (O : ValuationSubring F) (γ : O) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem MassDataIdxFrA.congSpan_neg (S : Set (ι → F)) (v : ι → F) : CongSpan O γ S (-v) ↔ CongSpan O γ S v := by sorry
