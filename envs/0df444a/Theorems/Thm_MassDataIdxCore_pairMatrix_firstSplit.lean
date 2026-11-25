-- Prove2me | Theorems.Thm_MassDataIdxCore_pairMatrix_firstSplit
-- name    : MassDataIdxCore.pairMatrix_firstSplit
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:37:30.65359+00:00
-- url     : https://prove2.me/theorems/07a0ac3e-0a51-45bb-aae1-5d420c38ffcf
-- title:
--   Mass Data Idx Core: pair Matrix first Split
-- statement:
--   The Mass Data Idx Core construction uses the pair Matrix first Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PairMatrixSecondSplit.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PairMatrixSecondSplit.lean#L30-L32

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
variable (θ : T ≃ₐ[K] K × K)

theorem MassDataIdxCore.pairMatrix_firstSplit (a b : Matrix n n K) : (pm θ a b).map (t1 θ) = a := by sorry
