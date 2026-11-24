-- Prove2me | Theorems.Thm_GlobalTheory_FinProjComplete_mem_smul_top_pi
-- name    : GlobalTheory.FinProjComplete.mem_smul_top_pi
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:39.01977+00:00
-- url     : https://prove2.me/theorems/d7a41da1-9fed-4ae6-a0c0-4f9b20f7a3e3
-- title:
--   Fin Proj Complete: mem smul top pi
-- statement:
--   The Fin Proj Complete construction uses the mem smul top pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra.lean#L5-L16

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

theorem GlobalTheory.FinProjComplete.mem_smul_top_pi {R ι : Type*} [CommRing R] [Finite ι] (J : Ideal R) (x : ι → R) :
    x ∈ (J • ⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by sorry
