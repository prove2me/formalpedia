-- Prove2me | Theorems.Thm_MassDataIdxLatFree_exists_gl
-- name    : MassDataIdxLatFree.exists_gl
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:38.095083+00:00
-- url     : https://prove2.me/theorems/ca444e99-2ff5-4fee-9021-08188c311d5c
-- title:
--   Mass Data Idx Lat Free: exists gl
-- statement:
--   The Mass Data Idx Lat Free construction uses the exists gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/ExistsGl.lean#L13-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/ExistsGl.lean#L13-L92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_ExistsGl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxLatFree
open scoped Matrix
open Module
variable {K : Type} [Field K] (O : ValuationSubring K) [IsPrincipalIdealRing O]
  {n : Type} [Fintype n] [DecidableEq n]

theorem MassDataIdxLatFree.exists_gl (M : Submodule O (n → K)) (hfg : M.FG)
    (hsp : Submodule.span K (M : Set (n → K)) = ⊤) :
    ∃ P : GL n K, ∀ y, y ∈ M ↔ ∀ i, (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) i ∈ O := by sorry
