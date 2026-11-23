-- Prove2me | Theorems.Thm_MassDataIdxCore_firstSplit_mulVec
-- name    : MassDataIdxCore.firstSplit_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:27.168173+00:00
-- url     : https://prove2.me/theorems/ac8acdaf-7cf8-48a7-88f8-4a86234a0df7
-- title:
--   Mass Data Idx Core: first Split mul Vec
-- statement:
--   The Mass Data Idx Core construction uses the first Split mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L34-L37

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

theorem MassDataIdxCore.firstSplit_mulVec (M : Matrix n n T) (x : n → T) :
    (fun i => t1 θ ((M *ᵥ x) i)) = M.map (t1 θ) *ᵥ fun j => t1 θ (x j) := by sorry
