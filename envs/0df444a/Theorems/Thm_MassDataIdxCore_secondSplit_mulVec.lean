-- Prove2me | Theorems.Thm_MassDataIdxCore_secondSplit_mulVec
-- name    : MassDataIdxCore.secondSplit_mulVec
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:43.352901+00:00
-- url     : https://prove2.me/theorems/0092226b-2c6c-4e09-920e-764342674aad
-- title:
--   Mass Data Idx Core: second Split mul Vec
-- statement:
--   The Mass Data Idx Core construction uses the second Split mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L39-L42

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

theorem MassDataIdxCore.secondSplit_mulVec (M : Matrix n n T) (x : n → T) :
    (fun i => t2 θ ((M *ᵥ x) i)) = M.map (t2 θ) *ᵥ fun j => t2 θ (x j) := by sorry
