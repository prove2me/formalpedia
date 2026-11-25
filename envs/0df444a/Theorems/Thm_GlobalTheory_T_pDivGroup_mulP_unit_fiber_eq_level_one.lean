-- Prove2me | Theorems.Thm_GlobalTheory_T_pDivGroup_mulP_unit_fiber_eq_level_one
-- name    : GlobalTheory.T.pDivGroup_mulP_unit_fiber_eq_level_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:54:58.713889+00:00
-- url     : https://prove2.me/theorems/5969385c-824b-525d-bd71-e8dabca0b7f8
-- title:
--   T: p Div Group mul P unit fiber eq level one
-- statement:
--   The T construction uses the p Div Group mul P unit fiber eq level one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupMulPUnitFibreEqLevelOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupMulPUnitFibreEqLevelOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupMulPUnitFibreEqLevelOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupMulPUnitFibreEqLevelOneStatement
import Theorems.Thm_GlobalTheory_IsBicharacter_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pDivGroup_mulP_unit_fiber_eq_level_one : ∀ (p : ℕ) (R k : Type) [CommRing R] [CommRing k] [Algebra R k], Function.Surjective (algebraMap R k) → ∀ (G : GlobalTheory.PDivGroup p R) (n : ℕ), Function.Surjective (fun a : G.A (n + 1) => ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1)) ∧ ∀ a : G.A (n + 1), ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1) = 0 ↔ a ∈ (RingHom.ker ((algebraMap R k).comp (Bialgebra.counitAlgHom R (G.A n) : G.A n →+* R))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by sorry
