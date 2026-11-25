-- Prove2me | Theorems.Thm_MassDataIdxCore_pairMatrix_secondSplit
-- name    : MassDataIdxCore.pairMatrix_secondSplit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:37:14.161957+00:00
-- url     : https://prove2.me/theorems/20621b5c-b114-45fb-9841-0f5cb89525c3
-- title:
--   Mass Data Idx Core: pair Matrix second Split
-- statement:
--   The Mass Data Idx Core construction uses the pair Matrix second Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PairMatrixSecondSplit.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PairMatrixSecondSplit.lean#L33-L35

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

theorem MassDataIdxCore.pairMatrix_secondSplit (a b : Matrix n n K) : (pm θ a b).map (t2 θ) = b := by sorry
