-- Prove2me | Theorems.Thm_MassDataIdxCore_intV_iff
-- name    : MassDataIdxCore.intV_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:53.152523+00:00
-- url     : https://prove2.me/theorems/079d66dd-22d4-49d9-bb0e-938140922aab
-- title:
--   Mass Data Idx Core: int V iff
-- statement:
--   The Mass Data Idx Core construction uses the int V iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PairMatrixSecondSplit.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PairMatrixSecondSplit.lean#L20-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PairMatrixSecondSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]

theorem MassDataIdxCore.intV_iff {M Mi : Matrix n n K} (hM : IntM O M) (hMi : IntM O Mi) (h : Mi * M = 1) (v : n → K) :
    IntV O (M *ᵥ v) ↔ IntV O v := by sorry
