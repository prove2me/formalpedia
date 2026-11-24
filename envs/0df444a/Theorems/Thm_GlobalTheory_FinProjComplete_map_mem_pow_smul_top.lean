-- Prove2me | Theorems.Thm_GlobalTheory_FinProjComplete_map_mem_pow_smul_top
-- name    : GlobalTheory.FinProjComplete.map_mem_pow_smul_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:25.976047+00:00
-- url     : https://prove2.me/theorems/30c07d0b-4163-4ad2-a954-9a9a55b117d2
-- title:
--   Fin Proj Complete: map mem pow smul top
-- statement:
--   The Fin Proj Complete construction uses the map mem pow smul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra.lean#L39-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinProjComplete

theorem GlobalTheory.FinProjComplete.map_mem_pow_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (f : M →ₗ[R] N) {x y : M} {n : ℕ}
    (h : x ≡ y [SMOD (J ^ n • ⊤ : Submodule R M)]) :
    f x ≡ f y [SMOD (J ^ n • ⊤ : Submodule R N)] := by sorry
