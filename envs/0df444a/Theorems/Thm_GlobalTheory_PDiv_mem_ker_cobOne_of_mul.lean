-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_mem_ker_cobOne_of_mul
-- name    : GlobalTheory.PDiv.mem_ker_cobOne_of_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:18.484397+00:00
-- url     : https://prove2.me/theorems/ef31c9df-8478-4c36-bd09-94ea1f22092c
-- title:
--   PDiv: mem ker cob One of mul
-- statement:
--   The PDiv construction uses the mem ker cob One of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionCartierDualTangentBijective.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionCartierDualTangentBijective.lean#L14-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.PDiv

theorem GlobalTheory.PDiv.mem_ker_cobOne_of_mul {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] {a : A}
    (h : ∀ φ ψ : CartierDual R A, (φ * ψ) a = φ 1 * ψ a + ψ 1 * φ a) :
    a ∈ LinearMap.ker (cobOne R A) := by sorry
