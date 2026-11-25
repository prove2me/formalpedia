-- Prove2me | Theorems.Thm_MassDataIdxCore_intV_mulVec
-- name    : MassDataIdxCore.intV_mulVec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:03.885661+00:00
-- url     : https://prove2.me/theorems/6bbe1aba-8f55-45ef-82c4-f7b2d3d5cc26
-- title:
--   Mass Data Idx Core: int V mul Vec
-- statement:
--   The Mass Data Idx Core construction uses the int V mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L17-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector
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

theorem MassDataIdxCore.intV_mulVec {M : Matrix n n K} {v : n → K} (hM : IntM O M) (hv : IntV O v) : IntV O (M *ᵥ v) := by sorry
