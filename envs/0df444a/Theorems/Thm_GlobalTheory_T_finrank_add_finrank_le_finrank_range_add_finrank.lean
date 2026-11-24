-- Prove2me | Theorems.Thm_GlobalTheory_T_finrank_add_finrank_le_finrank_range_add_finrank
-- name    : GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:39:58.953815+00:00
-- url     : https://prove2.me/theorems/c415b0a4-7baf-41b0-a803-8756b3451cad
-- title:
--   T: finrank add finrank le finrank range add finrank
-- statement:
--   The T construction uses the finrank add finrank le finrank range add finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAddLeFinrankRangeAddOfComapLeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAddLeFinrankRangeAddOfComapLeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAddLeFinrankRangeAddOfComapLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAddLeFinrankRangeAddOfComapLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by sorry
