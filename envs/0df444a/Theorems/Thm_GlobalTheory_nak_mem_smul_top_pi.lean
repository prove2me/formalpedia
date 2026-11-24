-- Prove2me | Theorems.Thm_GlobalTheory_nak_mem_smul_top_pi
-- name    : GlobalTheory.nak_mem_smul_top_pi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:12:10.413595+00:00
-- url     : https://prove2.me/theorems/ff41a99b-4e7d-4607-8772-63898de4428e
-- title:
--   Global Theory: nak mem smul top pi
-- statement:
--   The Global Theory construction uses the nak mem smul top pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteOfFiniteQuotMapOfIsPrecomplete.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteOfFiniteQuotMapOfIsPrecomplete.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteOfFiniteQuotMapOfIsPrecomplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.nak_mem_smul_top_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Ideal R) (x : ι → R) :
    x ∈ J • (⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by sorry
