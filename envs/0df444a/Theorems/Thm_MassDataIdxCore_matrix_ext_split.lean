-- Prove2me | Theorems.Thm_MassDataIdxCore_matrix_ext_split
-- name    : MassDataIdxCore.matrix_ext_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:37:02.841436+00:00
-- url     : https://prove2.me/theorems/64ab5b3c-465c-4920-bcad-52e8a77bdb36
-- title:
--   Mass Data Idx Core: matrix ext split
-- statement:
--   The Mass Data Idx Core construction uses the matrix ext split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PairMatrixSecondSplit.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PairMatrixSecondSplit.lean#L37-L44

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

theorem MassDataIdxCore.matrix_ext_split (M N : Matrix n n T) (h1 : M.map (t1 θ) = N.map (t1 θ)) (h2 : M.map (t2 θ) = N.map (t2 θ)) :
    M = N := by sorry
