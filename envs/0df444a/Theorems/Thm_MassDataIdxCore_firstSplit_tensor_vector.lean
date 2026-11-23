-- Prove2me | Theorems.Thm_MassDataIdxCore_firstSplit_tensor_vector
-- name    : MassDataIdxCore.firstSplit_tensor_vector
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:20.496493+00:00
-- url     : https://prove2.me/theorems/4fef0281-eeff-4b94-8e43-ef885f241f98
-- title:
--   Mass Data Idx Core: first Split tensor vector
-- statement:
--   The Mass Data Idx Core construction uses the first Split tensor vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L46-L48

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

theorem MassDataIdxCore.firstSplit_tensor_vector (j : n) : (fun i => t1 θ (tv θ P j i)) = fun i => (P : Matrix n n K) i j := by sorry
