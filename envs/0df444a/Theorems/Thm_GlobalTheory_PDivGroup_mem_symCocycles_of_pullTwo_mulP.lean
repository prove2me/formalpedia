-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_mem_symCocycles_of_pullTwo_mulP
-- name    : GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:49:38.658798+00:00
-- url     : https://prove2.me/theorems/2d833ecf-74f6-5118-8d66-6c8dba1faffc
-- title:
--   PDiv Group: mem sym Cocycles of pull Two mul P
-- statement:
--   The PDiv Group construction uses the mem sym Cocycles of pull Two mul P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSymmetricCocyclesOfPullbackMulP.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSymmetricCocyclesOfPullbackMulP.lean#L12-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSymmetricCocyclesOfPullbackMulP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory
open GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (c : G.A n ⊗[R] G.A n) (h : pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1))) :
    c ∈ symCocycles R (G.A n) := by sorry
