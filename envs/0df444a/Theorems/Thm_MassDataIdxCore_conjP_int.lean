-- Prove2me | Theorems.Thm_MassDataIdxCore_conjP_int
-- name    : MassDataIdxCore.conjP_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:00.209219+00:00
-- url     : https://prove2.me/theorems/f6e2981d-013a-4a5a-a04d-bbbc2fe27401
-- title:
--   Mass Data Idx Core: conj P int
-- statement:
--   The Mass Data Idx Core construction uses the conj P int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L71-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitTensorVector.lean#L71-L82

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

theorem MassDataIdxCore.conjP_int (g : GL n T) (hg : ∀ x, x ∈ Lat O θ J P → (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P) :
    IntM O (conjPrime₂ θ P g) := by sorry
