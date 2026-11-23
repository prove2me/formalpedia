-- Prove2me | Theorems.Thm_MassDataIdxCore_mulVec_col
-- name    : MassDataIdxCore.mulVec_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:30.092281+00:00
-- url     : https://prove2.me/theorems/b21b79c9-140c-4d73-9c60-f97be1a8a50c
-- title:
--   Mass Data Idx Core: mul Vec col
-- statement:
--   The Mass Data Idx Core construction uses the mul Vec col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L54-L56

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
variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K)

theorem MassDataIdxCore.mulVec_col (M N : Matrix n n K) (j : n) : (M *ᵥ fun i => N i j) = fun i => (M * N) i j := by sorry
