-- Prove2me | Theorems.Thm_GlobalTheory_finrank_add_le_finrank_range_add_of_comap_le
-- name    : GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:47:12.482725+00:00
-- url     : https://prove2.me/theorems/e1862795-414a-49a5-985d-bcc85b33b8df
-- title:
--   Global Theory: finrank add le finrank range add of comap le
-- statement:
--   The Global Theory construction uses the finrank add le finrank range add of comap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAddLeFinrankRangeAddOfComapLe.lean#L7-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAddLeFinrankRangeAddOfComapLe.lean#L7-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAddLeFinrankRangeAddOfComapLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory

theorem GlobalTheory.finrank_add_le_finrank_range_add_of_comap_le : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by sorry
