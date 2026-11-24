-- Prove2me | Theorems.Thm_GlobalTheory_T_sum_charpoly_roots_eq_finsum_eigenspace_finrank
-- name    : GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:37.846324+00:00
-- url     : https://prove2.me/theorems/2bed9884-451c-4586-8248-560e495386c2
-- title:
--   T: sum charpoly roots eq finsum eigenspace finrank
-- statement:
--   The T construction uses the sum charpoly roots eq finsum eigenspace finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumCharpolyRootsEqFinsumEigenspaceFinrankStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumCharpolyRootsEqFinsumEigenspaceFinrankStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumCharpolyRootsEqFinsumEigenspaceFinrank
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumCharpolyRootsEqFinsumEigenspaceFinrankStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank : ∀ (k : Type) [Field k] [IsAlgClosed k] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (g : Module.End k V) (N : ℕ), (N : k) ≠ 0 → g ^ N = 1 → ∀ h : k → ℂ, ((LinearMap.charpoly g).roots.map h).sum = ∑ᶠ μ ∈ {μ : k | μ ^ N = 1}, (Module.finrank k (Module.End.eigenspace g μ) : ℂ) * h μ := by sorry
