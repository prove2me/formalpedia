-- Prove2me | Theorems.Thm_MassDataIdxFrA_intVec_mulVec
-- name    : MassDataIdxFrA.intVec_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:37:30.673634+00:00
-- url     : https://prove2.me/theorems/571200f3-cdc3-4e8b-8212-fefdfaf593be
-- title:
--   Mass Data Idx Fr A: int Vec mul Vec
-- statement:
--   The Mass Data Idx Fr A construction uses the int Vec mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/CongSpanSingleIff.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/CongSpanSingleIff.lean#L29-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_CongSpanSingleIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxFrA
variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]
open Matrix
variable {F : Type} [Field F] (O : ValuationSubring F) (γ : O) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem MassDataIdxFrA.intVec_mulVec (M : Matrix ι ι F) (hM : ∀ i j, M i j ∈ O) {z : ι → F} (hz : IntVec O z) :
    IntVec O (M *ᵥ z) := by sorry
