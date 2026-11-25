-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_symmetricCocycles_of_pullback_mulP
-- name    : GlobalTheory.T.mem_symmetricCocycles_of_pullback_mulP
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:54:42.054715+00:00
-- url     : https://prove2.me/theorems/c2a4abf1-3aa0-5d19-b7cc-20aefcfe7aca
-- title:
--   T: mem symmetric Cocycles of pullback mul P
-- statement:
--   The T construction uses the mem symmetric Cocycles of pullback mul P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSymmetricCocyclesOfPullbackMulPStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSymmetricCocyclesOfPullbackMulPStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSymmetricCocyclesOfPullbackMulP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSymmetricCocyclesOfPullbackMulPStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_symmetricCocycles_of_pullback_mulP : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (c : G.A n ⊗[R] G.A n), pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1)) → c ∈ symCocycles R (G.A n) := by sorry
